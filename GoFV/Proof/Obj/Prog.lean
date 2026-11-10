import GoFV.Proof.Obj.Ex
import GoFV.Proof.Obj.Bitfield

variable [GoFV.SSA.Sem.Addrs]

/-!
# `progSym` is the symbolic `progEffect` (`GoFV/Asm/CheckObj.lean`)

For every Prog `progSym` describes (one lemma per opcode family), a successful `progStep`
under a layout with the same frame performs no access in the nil page (`NoNil`), ends in the
state the symbolic effect describes (`HoldsCore`), and its PC (and a call's `X30`) is where the
symbolic control goes (`PcP`).

The bridge is `ERel c e σ`: the effect `e` (`progEffect`) is `σ` evaluated in `c` (registers,
`SP`, flags, vector registers, loads, stores), and `PRel` relates `e`'s PC to `progSym`'s
control. `erel_apply` turns them into the three conclusions; the family lemmas (`fam_*`) derive
them from `progSym … = .ok` and `progEffect … = .ok`, operand by operand (`xP_eval`,
`srcP_eval`, `memP_eval`, `targetP_eval`, `wP_rel`).
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Asm.ARM64 (REG_R0 REG_R31 REG_RSP REG_EXT REG_LSL REG_F0 REG_V0 REG_ARNG C_XPRE C_XPOST)

/-! ## `Except` -/

private theorem pg_bind_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {b : β}
    (h : (x >>= g) = .ok b) : ∃ a, x = .ok a ∧ g a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem pg_ok_bind {ε α β : Type} (a : α) (g : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= g) = g a := (rfl)

private theorem pg_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := (rfl)

private theorem pg_ok_inj {ε α : Type} {a b : α} (h : (Except.ok a : Except ε α) = .ok b) : a = b := by
  cases h; rfl

/-! ## The relation between an effect and a symbolic state -/

/-- The effect `e` is `σ` evaluated in `c`. -/
private structure ERel (c : Ctx) (e : Eff) (σ : Sym) : Prop where
  x : e.x = σ.x.map (fun q => (q.1, q.2.eval c))
  xlt : ∀ q ∈ σ.x, q.1 < 31
  sp : e.sp.getD c.s.sp = σ.sp.eval c
  fl : e.flags.getD c.s.nzcv = σ.fl.eval c
  v : e.v = σ.v.map (fun q => (q.1, q.2.eval c))
  vlt : ∀ q ∈ σ.v, q.1 < 32
  loads : e.loads = σ.loads.map (fun q => (q.1.eval c, q.2))
  stores : e.stores = σ.stores.map
    (fun q => (q.1.eval c, q.2.1, (q.2.2.eval128 c).toNat % 2 ^ (8 * q.2.1)))

private theorem erel_init (c : Ctx) : ERel c {} {} :=
  ⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩

private theorem pg_ofNat5_inj {a b : Nat} (ha : a < 32) (hb : b < 32)
    (h : BitVec.ofNat 5 a = BitVec.ofNat 5 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- The vector-register writes keep the general registers, `SP`, the flags and the memory. -/
private theorem foldr_wV_other (l : List (Nat × BitVec 128)) (s : MState) :
    let t := l.foldr (fun (q : Nat × BitVec 128) (t : MState) => t.wV (BitVec.ofNat 5 q.1) q.2) s
    t.x = s.x ∧ t.sp = s.sp ∧ t.nzcv = s.nzcv ∧ t.mem = s.mem := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons q l ih => exact ih

private theorem apply_x {c : Ctx} {e : Eff} {l : List (Nat × Ex)} {s : MState} {next : BitVec 64}
    (hx : e.x = l.map (fun q => (q.1, q.2.eval c))) (hl : ∀ q ∈ l, q.1 < 31)
    (r : Nat) (hr : r < 32) :
    (e.apply s next).x (BitVec.ofNat 5 r) = ((l.lookup r).map (·.eval c)).getD (s.x (BitVec.ofNat 5 r)) := by
  unfold Eff.apply
  dsimp only
  rw [(foldr_wV_other e.v _).1]
  simp only [hx]
  clear hx
  induction l with
  | nil => rfl
  | cons q l ih =>
    have hq : q.1 < 31 := hl q (by simp)
    have ih := ih (fun q' h => hl q' (by simp [h]))
    simp only [List.map_cons, List.foldr_cons]
    have h31 : ¬ BitVec.ofNat 5 q.1 = 31 := fun h => by
      have := pg_ofNat5_inj (b := 31) (by omega) (by omega) h; omega
    rw [MState.wX, ite_eq_right_of_eq_false _ _ (eq_false h31)]
    by_cases hrq : r = q.1
    · subst hrq; simp [List.lookup]
    · have hne : ¬ BitVec.ofNat 5 r = BitVec.ofNat 5 q.1 := fun h => hrq (pg_ofNat5_inj hr (by omega) h)
      have hb : (r == q.1) = false := by simpa using hrq
      simp only [hne, ↓reduceIte, List.lookup, hb]
      exact ih

private theorem foldr_wX_other (l : List (Nat × BitVec 64)) (s : MState) :
    let t := l.foldr (fun (q : Nat × BitVec 64) (t : MState) => t.wX (BitVec.ofNat 5 q.1) q.2) s
    t.sp = s.sp ∧ t.v = s.v ∧ t.nzcv = s.nzcv ∧ t.mem = s.mem := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons q l ih =>
    simp only [List.foldr_cons, MState.wX]
    split <;> exact ih

/-- The vector registers after the effect, as `apply_x`. -/
private theorem apply_v {c : Ctx} {e : Eff} {l : List (Nat × VEx)} {s : MState} {next : BitVec 64}
    (hv : e.v = l.map (fun q => (q.1, q.2.eval c))) (hl : ∀ q ∈ l, q.1 < 32)
    (r : Nat) (hr : r < 32) :
    (e.apply s next).v (BitVec.ofNat 5 r) = ((l.lookup r).map (·.eval c)).getD (s.v (BitVec.ofNat 5 r)) := by
  unfold Eff.apply
  simp only [hv]
  clear hv
  induction l with
  | nil => exact congrFun (foldr_wX_other e.x s).2.1 _
  | cons q l ih =>
    have hq : q.1 < 32 := hl q (by simp)
    have ih := ih (fun q' h => hl q' (by simp [h]))
    simp only [List.map_cons, List.foldr_cons]
    rw [MState.wV]
    by_cases hrq : r = q.1
    · subst hrq; simp [List.lookup]
    · have hne : ¬ BitVec.ofNat 5 r = BitVec.ofNat 5 q.1 := fun h => hrq (pg_ofNat5_inj hr hq h)
      have hb : (r == q.1) = false := by simpa using hrq
      simp only [hne, ↓reduceIte, List.lookup, hb]
      exact ih

private theorem pg_ofNat_mod {w : Nat} (n : Nat) (x : BitVec w) :
    BitVec.ofNat (8 * n) (x.toNat % 2 ^ (8 * n)) = x.setWidth (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem apply_mem {c : Ctx} (l : List (Ex × Nat × Ex)) (m : Memory) :
    (l.map (fun q => (q.1.eval c, q.2.1, (q.2.2.eval128 c).toNat % 2 ^ (8 * q.2.1)))).foldl
      (fun m (q : BitVec 64 × Nat × Nat) => writeMem m q.1 q.2.1 (BitVec.ofNat (8 * q.2.1) q.2.2)) m =
      storesMem c l m := by
  induction l generalizing m with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, List.foldl_cons, storesMem, pg_ofNat_mod]
    exact ih _

/-- What `ERel` gives about the state after the effect. -/
private theorem erel_apply {L : Link} {s : MState} {e : Eff} {σ : Sym} {next : BitVec 64}
    (hR : ERel ⟨s, L.sym⟩ e σ) (hnil : e.nilAccess? = none) :
    NoNil ⟨s, L.sym⟩ σ ∧ HoldsCore ⟨s, L.sym⟩ σ (e.apply s next) ∧
      (e.apply s next).x 30 = (σ.getX 30).eval ⟨s, L.sym⟩ ∧ (e.apply s next).pc = e.pc.getD next := by
  have hnone := List.find?_eq_none.mp hnil
  have hx : ∀ r, r < 31 → (e.apply s next).x (BitVec.ofNat 5 r) = (σ.getX r).eval ⟨s, L.sym⟩ := by
    intro r hr
    rw [apply_x hR.x hR.xlt r (by omega)]
    simp only [Sym.getX]
    cases σ.x.lookup r <;> rfl
  have ho := foldr_wX_other (e.x) s
  have hw := foldr_wV_other e.v
    (e.x.foldr (fun (q : Nat × BitVec 64) (t : MState) => t.wX (BitVec.ofNat 5 q.1) q.2) s)
  refine ⟨⟨?_, ?_⟩, ⟨fun r hr => hx r (by omega), ?_, ?_, ?_, ?_, ?_⟩, hx 30 (by omega), rfl⟩
  · intro a n ha
    have := hnone (a.eval ⟨s, L.sym⟩)
      (by rw [List.mem_append, hR.loads]; exact .inl (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, ha, rfl⟩, rfl⟩))
    simpa using this
  · intro a n v ha
    have := hnone (a.eval ⟨s, L.sym⟩)
      (by rw [List.mem_append, hR.stores]; exact .inr (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, ha, rfl⟩, rfl⟩))
    simpa using this
  · have h31 := apply_x (s := s) (next := next) hR.x hR.xlt 31 (by omega)
    have hl : σ.x.lookup 31 = none := by
      rw [List.lookup_eq_none_iff]
      intro q hq; have := hR.xlt q hq; simp only [bne_iff_ne, ne_eq]; omega
    rw [hl] at h31
    exact h31
  · simp only [Eff.apply]
    rw [hw.2.1, ho.1]; exact hR.sp
  · simp only [Eff.apply]
    rw [hw.2.2.1, ho.2.2.1]; exact hR.fl
  · funext r
    obtain ⟨n, hn, rfl⟩ : ∃ n, n < 32 ∧ r = BitVec.ofNat 5 n := ⟨r.toNat, r.isLt, by simp⟩
    have hn' : (BitVec.ofNat 5 n).toNat = n := by simp; omega
    rw [apply_v hR.v hR.vlt n hn]
    unfold Sym.evalV
    rw [hn']
  · simp only [Eff.apply]
    rw [hw.2.2.2, ho.2.2.2, hR.stores]
    exact apply_mem _ _

/-- Where the effect's PC goes, against `progSym`'s control (calls apart). -/
private def PRel (L : Link) (s : MState) (e : Eff) : PCtl → Prop
  | .fall => e.pc = none
  | .jmp id => ∃ t, L.addr id = some t ∧ e.pc = some t
  | .cond cc id => ∃ t, L.addr id = some t ∧ e.pc = if (condOf cc).holds s.nzcv then some t else none
  | .cbz sf nz a id => ∃ t, L.addr id = some t ∧
      e.pc = if (ProgOp.trunc sf (a.eval ⟨s, L.sym⟩) == 0) != nz then some t else none
  | .tbz nz b a id => ∃ t, L.addr id = some t ∧
      e.pc = if (a.eval ⟨s, L.sym⟩).getLsbD b == nz then some t else none
  | .reg a => e.pc = some (a.eval ⟨s, L.sym⟩)
  | .call _ _ | .callReg _ => False

/-! ## Opcode names -/

private theorem baseOf_some {name : String} {ws : List String} {op : String} {sf : Bool}
    (h : ProgOp.baseOf name ws = some (op, sf)) : op ∈ ws ∧ name = if sf then op else op ++ "W" := by
  unfold ProgOp.baseOf at h
  split at h
  · rename_i hc
    cases h
    exact ⟨by simpa using hc, rfl⟩
  · split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      refine ⟨hc.2, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨t, ht⟩ := List.isSuffixOf_iff_suffix.mp hc.1
      apply String.toList_inj.mp
      simp only [ProgOp.chopS, String.toList_append, String.toList_ofList, ← String.length_toList, ← ht]
      simp
    · cases h

/-! ## Operands -/

private theorem gpIdx_eq {r : Int} {i : Nat} (h : ProgOp.gpIdx? r = some i) :
    i < 32 ∧ r = REG_R0 + i := by
  unfold ProgOp.gpIdx? at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [GoFV.Asm.ARM64.REG_R0, GoFV.Asm.ARM64.REG_R31] at hc ⊢
    omega
  · cases h

private theorem rx_eval (s : MState) (sym : Nat → BitVec 64) {r : Nat} (hr : r < 32) :
    s.rX (BitVec.ofNat 5 r) = (if r = 31 then Ex.k 0 else Ex.x r).eval ⟨s, sym⟩ := by
  by_cases h : r = 31
  · subst h; rfl
  · have : ¬ BitVec.ofNat 5 r = 31 := fun h' => h (pg_ofNat5_inj (b := 31) hr (by omega) h')
    simp only [MState.rX, this, h, ↓reduceIte, Ex.eval]

private theorem extReg_r0 {i : Nat} (hi : i < 32) : ProgOp.extReg? (REG_R0 + i) = none := by
  unfold ProgOp.extReg?
  have : ¬ (REG_R0 + (i : Int) ≥ REG_EXT ∧ REG_R0 + (i : Int) < REG_EXT + 4096) := by
    simp only [GoFV.Asm.ARM64.REG_R0, GoFV.Asm.ARM64.REG_EXT]; omega
  simp only [Bool.and_eq_true, decide_eq_true_eq, this, ↓reduceIte]

private theorem fpIdx_r0 {i : Nat} (hi : i < 32) : ProgOp.fpIdx? (REG_R0 + i) = none := by
  unfold ProgOp.fpIdx?
  have h1 : ¬ (REG_F0 ≤ REG_R0 + (i : Int) ∧ REG_R0 + (i : Int) < REG_V0 + 32) := by
    simp only [GoFV.Asm.ARM64.REG_R0, GoFV.Asm.ARM64.REG_F0, GoFV.Asm.ARM64.REG_V0]; omega
  have h2 : ¬ (REG_ARNG ≤ REG_R0 + (i : Int) ∧ REG_R0 + (i : Int) < REG_ARNG + 1024) := by
    simp only [GoFV.Asm.ARM64.REG_R0, GoFV.Asm.ARM64.REG_ARNG]; omega
  simp only [Bool.and_eq_true, decide_eq_true_eq, h1, h2, ↓reduceIte]

/-- A register operand `progSym` accepts: `progEffect` reads its value, and it is neither an
extended nor a vector register. -/
private theorem xP_eval {L : Link} {s : MState} {p : Prog} {r : Int} {a : Ex} (h : xP r = .ok a) :
    ProgCtx.x ⟨L, s, p⟩ r = .ok (a.eval ⟨s, L.sym⟩) ∧ ProgOp.extReg? r = none ∧
      ProgOp.fpIdx? r = none := by
  unfold xP at h
  unfold ProgCtx.x
  by_cases hc : r = REG_RSP
  · subst hc
    simp only [beq_self_eq_true, ↓reduceIte, pg_pure] at h ⊢
    cases h
    exact ⟨rfl, by decide, by decide⟩
  · have hc' : (r == REG_RSP) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hg : ProgOp.gpIdx? r with
    | none => simp only [hg] at h; cases h
    | some i =>
      obtain ⟨hi, rfl⟩ := gpIdx_eq hg
      refine ⟨?_, extReg_r0 hi, fpIdx_r0 hi⟩
      simp only [hg] at h ⊢
      rw [rx_eval s L.sym hi]
      by_cases h31 : i = 31
      · subst h31; cases h; rfl
      · split at h
        · next _ heq' => exact absurd (Option.some.inj heq') h31
        · next _ i' _ heq' => cases heq'; cases h; simp only [h31, ↓reduceIte]; rfl
        · next _ heq' => cases heq'

/-- A register operand `progSym` accepts is not a whole vector register: a store writes its
value zero-extended. -/
private theorem xP_eval128 {r : Int} {a : Ex} (h : xP r = .ok a) (c : Ctx) :
    (a.eval128 c).toNat = (a.eval c).toNat := by
  have : a.eval128 c = (a.eval c).setWidth 128 := by
    unfold xP at h
    split at h
    · cases h; rfl
    · split at h <;> cases h <;> rfl
  rw [this, BitVec.toNat_setWidth_of_le (by omega)]

private theorem trunc_trunc (sf : Bool) (x : BitVec 64) :
    ProgOp.trunc sf (ProgOp.trunc sf x) = ProgOp.trunc sf x := by
  cases sf <;> simp [ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

private theorem trunc_sized (sf : Bool) (f : (n : Nat) → (BitVec 64 → BitVec n) → BitVec n) :
    ProgOp.trunc sf (sized sf f) = sized sf f := by
  cases sf <;> simp [ProgOp.trunc, sized, BitVec.setWidth_setWidth_of_le]

private theorem addSub_trunc (sf sub : Bool) (x y : BitVec 64) :
    addSub sf sub (ProgOp.trunc sf x) (ProgOp.trunc sf y) = addSub sf sub x y := by
  cases sf <;> simp [addSub, sizedF, ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

private theorem logical_trunc (sf : Bool) (opc : BitVec 2) (x y : BitVec 64) :
    logical sf opc (ProgOp.trunc sf x) (ProgOp.trunc sf y) = logical sf opc x y := by
  cases sf <;> simp [logical, sizedF, ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

/-- A source operand `progSym` accepts: `progEffect`'s value, at the datasize. -/
private theorem srcP_eval {L : Link} {s : MState} {p : Prog} {sf : Bool} {a : Addr} {y : Ex}
    (h : srcP sf a = .ok y) :
    ProgCtx.src ⟨L, s, p⟩ sf a = .ok (ProgOp.trunc sf (y.eval ⟨s, L.sym⟩)) := by
  unfold srcP at h
  unfold ProgCtx.src
  split at h
  · rename_i ht
    simp only [ht]
    split at h
    · rename_i r opt amt hx
      cases h
      simp only [hx]
      have hr : r < 32 := by
        unfold ProgOp.extReg? at hx; split at hx
        · cases hx; omega
        · cases hx
      rw [Ex.eval_mkExt, ← rx_eval s L.sym hr]
      rfl
    · rename_i hx
      simp only [hx]
      rw [(xP_eval h).1]
      rfl
  · rename_i ht
    cases h
    simp only [ht, Ex.eval, trunc_trunc]
    rfl
  · rename_i ht
    cases h
    simp only [ht]
    rw [Ex.eval_mkShift, ← rx_eval s L.sym (Nat.mod_lt _ (by decide)), trunc_sized]
    rfl
  · cases h

private theorem extendReg_3 (x : BitVec 64) (sh : Nat) : extendReg x 3 sh = x <<< sh := by
  have hm : GoFV.SSA.Sem.Arm64.mask 64 = BitVec.allOnes 64 := rfl
  have h3 : (3 : BitVec 3).getLsbD 2 = false := by decide
  have h4 : (3 : BitVec 3).toNat % 4 = 3 := by decide
  simp only [extendReg, h3, h4, Bool.false_eq_true, ↓reduceIte, Nat.reducePow, Nat.reduceMul, hm,
    BitVec.and_allOnes]

/-- A memory operand `progSym` accepts: `progEffect`'s address and write-back. -/
private theorem memP_eval {L : Link} {s : MState} {p : Prog} {az ez : Int} {a : Addr} {e : Ex}
    {wb : Option (Int × Ex)} (h : memP az ez p.scond a = .ok (e, wb)) (ha : a.type = .MEM)
    (haz : L.autosize = az) (hez : L.extrasize = ez) :
    ProgCtx.mem ⟨L, s, p⟩ a = .ok (e.eval ⟨s, L.sym⟩, wb.map fun q => (q.1, q.2.eval ⟨s, L.sym⟩)) := by
  subst haz hez
  unfold memP at h
  unfold ProgCtx.mem
  simp only [ha, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pg_pure,
    pg_ok_bind] at h ⊢
  split at h
  · rename_i hn; cases h; simp only [hn, Ex.eval_mkAdd, Ex.eval]; rfl
  · rename_i hn; cases h; simp only [hn, Ex.eval_mkAdd, Ex.eval]; rfl
  · rename_i hn
    split at h
    · rename_i y hy; cases h; simp only [hn, hy, Ex.eval_mkAdd, Ex.eval]; rfl
    · cases h
  · rename_i hn
    split at h
    · rename_i y hy; cases h; simp only [hn, hy, Ex.eval_mkAdd, Ex.eval]; rfl
    · cases h
  · rename_i hn
    simp only [hn]
    obtain ⟨base, hb, h⟩ := pg_bind_ok h
    rw [(xP_eval (L := L) (s := s) (p := p) hb).1, pg_ok_bind]
    split at h
    · rename_i hi
      simp only [hi, ↓reduceIte]
      split at h
      · rename_i he
        cases h
        simp only [he, ↓reduceIte, Option.map]
        rw [Ex.eval_mkAdd, Ex.eval_mkExt, ← rx_eval s L.sym (Nat.mod_lt _ (by decide))]
      · rename_i he
        split at h
        · rename_i hl
          cases h
          simp only [he, hl, Bool.false_eq_true, ↓reduceIte, Option.map]
          rw [Ex.eval_mkAdd, Ex.eval_mkExt, ← rx_eval s L.sym (Nat.mod_lt _ (by decide)),
            extendReg_3]
        · rename_i hl
          obtain ⟨idx, hidx, h⟩ := pg_bind_ok h
          cases h
          simp only [he, hl, Bool.false_eq_true, ↓reduceIte]
          rw [(xP_eval (L := L) (s := s) (p := p) hidx).1, pg_ok_bind, Ex.eval_mkAdd]
          rfl
    · rename_i hi
      simp only [hi, Bool.false_eq_true, ↓reduceIte]
      split at h
      · rename_i hc; cases h; simp only [hc, ↓reduceIte, Ex.eval_mkAdd, Ex.eval, Option.map]
      · rename_i hc
        split at h
        · rename_i hc'; cases h; simp only [hc, hc', Bool.false_eq_true, ↓reduceIte, Ex.eval_mkAdd,
            Ex.eval, Option.map]
        · rename_i hc'; cases h; simp only [hc, hc', Bool.false_eq_true, ↓reduceIte, Ex.eval_mkAdd,
            Ex.eval, Option.map]
  · cases h

private theorem targetP_eval {L : Link} {s : MState} {p : Prog} {a : Addr} {id : Nat}
    {t : BitVec 64} (h : targetP a = .ok id) (ht : ProgCtx.target ⟨L, s, p⟩ a = .ok t) :
    L.addr id = some t := by
  unfold targetP at h
  split at h
  · rename_i id' hty hv
    cases h
    unfold ProgCtx.target at ht
    simp only [hty, hv] at ht
    split at ht
    · rename_i pc hpc; cases ht; exact hpc
    · cases ht
  · cases h

/-- A register write `progSym` accepts, `progEffect`'s alike. -/
private theorem wP_rel {c : Ctx} {e e' : Eff} {σ σ' : Sym} {r : Int} {v : Ex} {val : BitVec 64}
    (hR : ERel c e σ) (h : wP σ r v = .ok σ') (he : e.wX r val = .ok e') (hv : val = v.eval c) :
    ERel c e' σ' ∧ σ'.loads = σ.loads ∧ σ'.stores = σ.stores ∧ σ'.fl = σ.fl ∧ e'.pc = e.pc := by
  subst hv
  unfold wP at h
  unfold Eff.wX at he
  split at h
  · rename_i hc; cases h; simp only [hc, ↓reduceIte] at he; cases he; exact ⟨hR, rfl, rfl, rfl, rfl⟩
  · rename_i hc
    split at h
    · rename_i hc'
      cases h
      simp only [hc, hc', Bool.false_eq_true, ↓reduceIte] at he
      cases he
      exact ⟨⟨hR.x, hR.xlt, rfl, hR.fl, hR.v, hR.vlt, hR.loads, hR.stores⟩, rfl, rfl, rfl, rfl⟩
    · rename_i hc'
      simp only [hc, hc', Bool.false_eq_true, ↓reduceIte] at he
      split at h
      · rename_i i hg
        cases h
        simp only [hg] at he
        cases he
        have hi := gpIdx_eq hg
        have hi31 : i < 31 := by
          have : r ≠ REG_R31 := fun h' => by simp [h'] at hc
          simp only [GoFV.Asm.ARM64.REG_R0, GoFV.Asm.ARM64.REG_R31] at hi this
          omega
        refine ⟨⟨?_, ?_, hR.sp, hR.fl, hR.v, hR.vlt, hR.loads, hR.stores⟩, rfl, rfl, rfl, rfl⟩
        · simp only [List.map_cons, hR.x]
        · intro q hq
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact hi31
          · exact hR.xlt q hq
      · cases h

private theorem src_reg {L : Link} {s : MState} {p : Prog} {sf : Bool} {r : Int} {a : Ex}
    (h : xP r = .ok a) :
    ProgCtx.src ⟨L, s, p⟩ sf { type := .REG, reg := r } =
      .ok (ProgOp.trunc sf (a.eval ⟨s, L.sym⟩)) := by
  have hx := xP_eval (L := L) (s := s) (p := p) h
  simp only [ProgCtx.src, hx.2.1, hx.1]
  rfl

/-! ### Vector registers -/

private theorem fpIdx_lt {r : Int} {i : Nat} (h : ProgOp.fpIdx? r = some i) : i < 32 := by
  unfold ProgOp.fpIdx? at h
  split at h
  · cases h; exact Nat.mod_lt _ (by decide)
  · split at h
    · cases h; exact Nat.mod_lt _ (by decide)
    · cases h

/-- A vector register operand `progSym` accepts: `progEffect` reads its value. -/
private theorem vP_eval {L : Link} {s : MState} {p : Prog} {r : Int} {i : Nat} (h : vP r = .ok i) :
    ProgCtx.v ⟨L, s, p⟩ r = .ok ((VEx.v i).eval ⟨s, L.sym⟩) ∧ ProgOp.fpIdx? r = some i := by
  unfold vP at h
  split at h
  · rename_i j hj
    cases h
    exact ⟨by unfold ProgCtx.v; rw [hj]; rfl, hj⟩
  · cases h

/-- A vector register write `progSym` accepts, `progEffect`'s alike. -/
private theorem wVP_rel {c : Ctx} {e e' : Eff} {σ σ' : Sym} {r : Int} {v : VEx} {val : BitVec 128}
    (hR : ERel c e σ) (h : wVP σ r v = .ok σ') (he : e.wV r val = .ok e') (hv : val = v.eval c) :
    ERel c e' σ' ∧ e'.pc = e.pc := by
  subst hv
  unfold wVP at h
  unfold Eff.wV at he
  split at h
  · rename_i i hi
    cases h
    simp only [hi] at he
    cases he
    refine ⟨⟨hR.x, hR.xlt, hR.sp, hR.fl, by simp only [Sym.wV, List.map_cons, hR.v], ?_, hR.loads,
      hR.stores⟩, rfl⟩
    intro q hq
    simp only [Sym.wV, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact fpIdx_lt hi
    · exact hR.vlt q hq
  · cases h

/-- `FMOV` between vector registers: `progEffect`'s low `n` bytes are `FMOV`'s `fp1Op`. -/
private theorem fmov_vv {n : Nat} (hn : n = 4 ∨ n = 8) (x : BitVec 128) :
    (ProgOp.maskN n (x.setWidth 64)).setWidth 128 = fp1Op (fpFt n) 0 x := by
  rcases hn with rfl | rfl
  · rw [zext32]
    apply BitVec.eq_of_toNat_eq
    simp [ProgOp.trunc, fpFt, fp1Op, fpUn, BitVec.toNat_setWidth] <;> omega
  · apply BitVec.eq_of_toNat_eq
    simp [ProgOp.maskN, fpFt, fp1Op, fpUn, BitVec.toNat_setWidth] <;> omega

/-- `FMOV` to a general register: the low `n` bytes of the vector register are `Ex.vlo`. -/
private theorem fmov_vx {n : Nat} (hn : n = 4 ∨ n = 8) (c : Ctx) (r : Nat) :
    ProgOp.maskN n ((c.s.v (BitVec.ofNat 5 r)).setWidth 64) = (Ex.vlo (fpFt n) r).eval c := by
  rcases hn with rfl | rfl
  · rw [zext32]
    apply BitVec.eq_of_toNat_eq
    simp [ProgOp.trunc, fpFt, Ex.eval, BitVec.toNat_setWidth] <;> omega
  · simp [ProgOp.maskN, fpFt, Ex.eval]

/-- `FMOV` from a general register: the low `n` bytes are `VEx.ofX`. -/
private theorem fmov_xv {n : Nat} (hn : n = 4 ∨ n = 8) (x : BitVec 64) :
    (ProgOp.maskN n x).setWidth 128 = (x.setWidth (8 * n)).setWidth 128 := by
  rcases hn with rfl | rfl
  · rw [zext32]
    apply BitVec.eq_of_toNat_eq
    simp [ProgOp.trunc, BitVec.toNat_setWidth] <;> omega
  · simp [ProgOp.maskN]

/-- The bytes a SIMD&FP store writes: the low `n` bytes of the vector register (`vStoreEx`). -/
private theorem vstore_mod {n : Nat} (hn : n = 4 ∨ n = 8 ∨ n = 16) (c : Ctx) (r : Nat) :
    ((vStoreEx n r).eval128 c).toNat % 2 ^ (8 * n) =
      (c.s.v (BitVec.ofNat 5 r)).toNat % 2 ^ (8 * n) := by
  rcases hn with rfl | rfl | rfl <;>
    simp [vStoreEx, Ex.eval128, Ex.eval, BitVec.toNat_setWidth] <;> omega

private theorem pg_ofInt_toNat {off : Int} (h : ¬ off < 0) :
    BitVec.ofInt 64 off = BitVec.ofNat 64 off.toNat := by
  have h0 : off = ((off.toNat : Nat) : Int) := (Int.toNat_of_nonneg (by omega)).symm
  rw [h0, BitVec.ofInt_natCast, Int.toNat_natCast]

/-! ## The families -/

/-- What a family lemma gives: the relation, or a call (`X30` the fall-through). -/
private def Out (L : Link) (p : Prog) (s : MState) (e : Eff) (σ : Sym) (pc : PCtl) : Prop :=
  (ERel ⟨s, L.sym⟩ e σ ∧ PRel L s e pc) ∨
  (∃ n add f, pc = .call n add ∧ σ = {} ∧ L.nextAddr p.id = some f ∧
    e = { x := [(30, f)], pc := some (L.sym n + BitVec.ofInt 64 add) }) ∨
  (∃ a f, pc = .callReg a ∧ σ = {} ∧ isICall p = true ∧ L.nextAddr p.id = some f ∧
    e = { x := [(30, f)], pc := some (a.eval ⟨s, L.sym⟩) })

section fam
variable {az ez : Int} {p : Prog} {σ : Sym} {pc : PCtl} {L : Link} {s : MState} {e : Eff}

private theorem shift_pre {name op : String} {sf : Bool}
    (hb : ProgOp.baseOf name ["LSL", "LSR", "ASR"] = some (op, sf)) :
    ProgOp.baseOf name ProgOp.binNames = some (op, sf) := by
  obtain ⟨hop, rfl⟩ := baseOf_some hb
  have key : ∀ op ∈ ["LSL", "LSR", "ASR"], ∀ sf : Bool,
      ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = some (op, sf) := by decide
  exact key op hop sf

private theorem shiftBfm_ok {op : String} {sf : Bool} {k : Nat} {x r : Ex}
    (h : shiftBfm op sf k x = .ok r) :
    0 < k ∧ k < wOf sf ∧
      ((op = "LSL" ∧ r = Ex.mkBfm sf 2 (BitVec.ofNat 6 ((wOf sf - k) % wOf sf))
          (BitVec.ofNat 6 (wOf sf - 1 - k)) (.k 0) x) ∨
       (op = "LSR" ∧ r = Ex.mkBfm sf 2 (BitVec.ofNat 6 k) (BitVec.ofNat 6 (wOf sf - 1)) (.k 0) x) ∨
       (op = "ASR" ∧ r = Ex.mkBfm sf 0 (BitVec.ofNat 6 k) (BitVec.ofNat 6 (wOf sf - 1)) (.k 0) x)) := by
  unfold shiftBfm at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  by_cases hk : (k = 0 ∨ k ≥ if sf = true then 64 else 32)
  · simp only [hk, ↓reduceIte] at h; cases h
  simp only [hk, ↓reduceIte] at h
  refine ⟨by omega, by simp only [wOf]; omega, ?_⟩
  split at h
  · cases h; exact .inl ⟨rfl, rfl⟩
  · cases h; exact .inr (.inl ⟨rfl, rfl⟩)
  · cases h; exact .inr (.inr ⟨rfl, rfl⟩)
  · cases h

/-- Constant shifts: the bitfield move `shiftBfm`. -/
private theorem fam_shift {op : String} {sf : Bool}
    (hb : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] = some (op, sf))
    (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  obtain ⟨hop, -⟩ := baseOf_some hb
  have hbin := shift_pre hb
  have hsh : ["LSL", "LSR", "ASR", "ROR"].contains op = true := by
    have key : ∀ op ∈ ["LSL", "LSR", "ASR"], ["LSL", "LSR", "ASR", "ROR"].contains op = true := by
      decide
    exact key op hop
  unfold progSymCore at h
  simp only [hb] at h
  unfold progEffect at he
  simp only [hbin, ProgCtx.rn] at he
  by_cases hc : p.from_.type = .CONST
  case neg =>
    have hc' : (p.from_.type == .CONST) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
    simp only [hc', Bool.false_and, Bool.false_eq_true, ↓reduceIte] at he
    obtain ⟨x, hx, h⟩ := pg_bind_ok h
    obtain ⟨y, hy, h⟩ := pg_bind_ok h
    obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    simp only [src_reg hx, srcP_eval hy, pg_ok_bind] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;>
    · simp (config := { decide := true }) only [ProgOp.binOp, ↓reduceIte] at he hσ1
      obtain ⟨e1, he1, he⟩ := pg_bind_ok he
      obtain rfl := pg_ok_inj he
      obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
        (by rw [Ex.eval_mkDp2, dp2_trunc])
      exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩
  by_cases hneg : p.from_.offset < 0
  · simp only [hc, hneg, beq_self_eq_true, ↓reduceIte] at h; cases h
  simp only [hc, hneg, beq_self_eq_true, ↓reduceIte] at h
  obtain ⟨x, hx, h⟩ := pg_bind_ok h
  obtain ⟨r, hr, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  obtain ⟨hk0, hkw, hr⟩ := shiftBfm_ok hr
  rw [pg_ofInt_toNat hneg] at he
  simp only [hc, hsh, beq_self_eq_true, Bool.true_and, ↓reduceIte, src_reg hx, pg_ok_bind] at he
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp (config := { decide := true }) only [ProgOp.binOp] at he
    obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he (by
      rw [Ex.eval_mkBfm]
      first
      | exact lsl_bfm sf _ ⟨hk0, hkw⟩ (x.eval ⟨s, L.sym⟩)
      | exact lsr_bfm sf _ ⟨hk0, hkw⟩ (x.eval ⟨s, L.sym⟩)
      | exact asr_bfm sf _ ⟨hk0, hkw⟩ (x.eval ⟨s, L.sym⟩))
    exact .inl ⟨hR, hpc⟩

private theorem add_pre {name op : String} {sf : Bool}
    (hb : ProgOp.baseOf name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] =
      some (op, sf)) :
    ProgOp.baseOf name ProgOp.binNames = some (op, sf) := by
  obtain ⟨hop, rfl⟩ := baseOf_some hb
  have key : ∀ op ∈ ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"], ∀ sf : Bool,
      ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = some (op, sf) := by decide
  exact key op hop sf

/-- `ADD`/`SUB`/`AND`/`ORR`/`EOR`/`ADDS`/`SUBS`/`ANDS` (and `W`). -/
private theorem fam_add {op : String} {sf : Bool}
    (hb1 : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] = none)
    (hb : ProgOp.baseOf p.as.name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] =
      some (op, sf))
    (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  obtain ⟨hop, -⟩ := baseOf_some hb
  have hbin := add_pre hb
  have hnsh : ["LSL", "LSR", "ASR", "ROR"].contains op = false := by
    have key : ∀ op ∈ ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"],
        ["LSL", "LSR", "ASR", "ROR"].contains op = false := by decide
    exact key op hop
  unfold progSymCore at h
  simp only [hb1, hb] at h
  unfold progEffect at he
  simp only [hbin, ProgCtx.rn] at he
  obtain ⟨x, hx, h⟩ := pg_bind_ok h
  obtain ⟨y, hy, h⟩ := pg_bind_ok h
  simp only [src_reg hx, srcP_eval hy, pg_ok_bind, hnsh, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [ProgOp.binOp] at he h
    obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    obtain ⟨e1, he1, he⟩ := pg_bind_ok he
    obtain rfl := pg_ok_inj he
    obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
      (by simp only [Ex.eval_mkAddSub, Ex.eval_mkLogical, addSub_trunc, logical_trunc])
    refine .inl ⟨⟨hR.x, hR.xlt, hR.sp, ?_, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩
    simp only [hfl, Option.getD_none, Option.getD_some, Fl.eval_mkAddSub, Fl.eval_mkAnds,
      addSub_trunc, logical_trunc]
    try rfl

private theorem cmp_pre {name op : String} {sf : Bool}
    (hb : ProgOp.baseOf name ["CMP", "CMN", "TST"] = some (op, sf)) :
    ProgOp.baseOf name ProgOp.binNames = none := by
  obtain ⟨hop, rfl⟩ := baseOf_some hb
  have key : ∀ op ∈ ["CMP", "CMN", "TST"], ∀ sf : Bool,
      ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = none := by decide
  exact key op hop sf

/-- `CMP`/`CMN`/`TST` (and `W`). -/
private theorem fam_cmp {op : String} {sf : Bool}
    (hb1 : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] = none)
    (hb2 : ProgOp.baseOf p.as.name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] = none)
    (hb : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] = some (op, sf))
    (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  obtain ⟨hop, -⟩ := baseOf_some hb
  have hbin := cmp_pre hb
  unfold progSymCore at h
  simp only [hb1, hb2, hb] at h
  unfold progEffect at he
  simp only [hbin, hb] at he
  obtain ⟨x, hx, h⟩ := pg_bind_ok h
  obtain ⟨y, hy, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  simp only [src_reg hx, srcP_eval hy, pg_ok_bind] at he
  obtain rfl := pg_ok_inj he
  refine .inl ⟨⟨rfl, by simp, rfl, ?_, rfl, by simp, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [ProgOp.binOp, Option.getD_some, ↓reduceIte,
      Fl.eval_mkAddSub, Fl.eval_mkAnds, addSub_trunc, logical_trunc]

private theorem neg_pre {name op : String} {sf : Bool}
    (hb : ProgOp.baseOf name ["NEG"] = some (op, sf)) :
    op = "NEG" ∧ ProgOp.baseOf name ProgOp.binNames = none ∧
      ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = some (op, sf) := by
  obtain ⟨hop, rfl⟩ := baseOf_some hb
  have key : ∀ op ∈ ["NEG"], ∀ sf : Bool, op = "NEG" ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["NEG", "NEGS", "MVN", "NGC", "NGCS"] =
        some (op, sf) := by decide
  exact key op hop sf

/-- `NEG` (and `W`). -/
private theorem fam_neg {op : String} {sf : Bool}
    (hb1 : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] = none)
    (hb2 : ProgOp.baseOf p.as.name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] = none)
    (hb3 : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] = none)
    (hb : ProgOp.baseOf p.as.name ["NEG"] = some (op, sf))
    (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  obtain ⟨rfl, hbin, hneg⟩ := neg_pre hb
  unfold progSymCore at h
  simp only [hb1, hb2, hb3, hb] at h
  unfold progEffect at he
  simp only [hbin, hb3, hneg] at he
  obtain ⟨y, hy, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  simp (config := { decide := true }) only [srcP_eval hy, pg_ok_bind, ProgOp.binOp] at he
  obtain ⟨e1, he1, he⟩ := pg_bind_ok he
  obtain rfl := pg_ok_inj he
  obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1 (by
    rw [Ex.eval_mkAddSub, ← addSub_trunc sf true 0, trunc_trunc, addSub_trunc]
    rfl)
  exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩

private theorem ubfx_pre {name op : String} {sf : Bool}
    (hb : ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ"] = some (op, sf)) :
    ProgOp.baseOf name ProgOp.binNames = none ∧
      ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
      ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
      ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
      ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = some (op, sf) := by
  obtain ⟨hop, rfl⟩ := baseOf_some hb
  have key : ∀ op ∈ ["UBFX", "SBFX", "UBFIZ"], ∀ sf : Bool,
      ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["MADD", "MSUB"] = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] =
        some (op, sf) := by decide
  exact key op hop sf

/-- `UBFX`/`SBFX`/`UBFIZ` (and `W`). -/
private theorem fam_ubfx {op : String} {sf : Bool}
    (hb1 : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] = none)
    (hb2 : ProgOp.baseOf p.as.name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] = none)
    (hb3 : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] = none)
    (hb4 : ProgOp.baseOf p.as.name ["NEG"] = none)
    (hb : ProgOp.baseOf p.as.name ["UBFX", "SBFX", "UBFIZ"] = some (op, sf))
    (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  obtain ⟨hop, -⟩ := baseOf_some hb
  obtain ⟨p1, p2, p3, p4, p5⟩ := ubfx_pre hb
  unfold progSymCore at h
  simp only [hb1, hb2, hb3, hb4, hb] at h
  unfold progEffect at he
  simp only [p1, hb3, p2, p3, p4, p5, ProgCtx.rest] at he
  cases hrest : p.rest[0]? with
  | none => simp only [hrest] at h; cases h
  | some q =>
  obtain ⟨_, a⟩ := q
  simp only [hrest, pg_pure, pg_ok_bind] at h he
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  by_cases hw : (a.offset.toNat = 0 ∨ p.from_.offset.toNat + a.offset.toNat > if sf = true then 64 else 32)
  · simp only [hw, ↓reduceIte] at h; cases h
  simp only [hw, ↓reduceIte] at h
  obtain ⟨x, hx, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  rw [(xP_eval hx).1, pg_ok_bind] at he
  obtain ⟨d, -, he⟩ := pg_bind_ok he
  have hw' : 0 < a.offset.toNat ∧ p.from_.offset.toNat + a.offset.toNat ≤ wOf sf := by
    simp only [wOf]; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl
  · simp (config := { decide := true }) only at he hσ1
    obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he (by
      rw [Ex.eval_mkBfm]; exact ubfx_bfm sf _ _ hw'.1 hw'.2 _)
    exact .inl ⟨hR, hpc⟩
  · simp (config := { decide := true }) only at he hσ1
    obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he (by
      rw [Ex.eval_mkBfm]; exact sbfx_bfm sf _ _ hw'.1 hw'.2 _)
    exact .inl ⟨hR, hpc⟩
  · simp (config := { decide := true }) only at he hσ1
    obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he (by
      rw [Ex.eval_mkBfm]; exact ubfiz_bfm sf _ _ hw'.1 hw'.2 _)
    exact .inl ⟨hR, hpc⟩

/-- The opcode names none of `progEffect`'s branches before the `movMem` one takes. -/
private def pre9 (name : String) : Prop :=
  ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
  ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
  ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
  ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
  ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = none ∧
  ProgOp.baseOf name ["EXTR"] = none ∧
  ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
  ProgOp.baseOf name ["CSET", "CSETM"] = none

private theorem mov_pre {name : String} {n : Nat} {sg : Bool}
    (hm : ProgOp.movMem name = some (n, sg, false)) :
    pre9 name ∧ ((n = 8 ∧ sg = false) ∨ (n = 4 ∧ sg = true) ∨ (n = 4 ∧ sg = false) ∨
      (n = 2 ∧ sg = true) ∨ (n = 2 ∧ sg = false) ∨ (n = 1 ∧ sg = true) ∨ (n = 1 ∧ sg = false)) := by
  unfold ProgOp.movMem at hm
  split at hm <;> (try cases hm) <;> simp (config := { decide := true }) [pre9]

private theorem pair_pre {name : String} {ld : Bool} {n : Nat} {sg : Bool}
    (hm : ProgOp.pairOp name = some (ld, n, sg, false)) : pre9 name := by
  unfold ProgOp.pairOp at hm
  split at hm <;> (try cases hm) <;> simp (config := { decide := true }) [pre9]

private theorem wP_fp {σ σ' : Sym} {r : Int} {v : Ex} (h : wP σ r v = .ok σ') :
    ProgOp.fpIdx? r = none := by
  unfold wP at h
  split at h
  · rename_i hc; simp only [beq_iff_eq] at hc; subst hc; decide
  · rename_i hc
    split at h
    · rename_i hc'; simp only [beq_iff_eq] at hc'; subst hc'; decide
    · split at h
      · rename_i i hg; obtain ⟨hi, rfl⟩ := gpIdx_eq hg; exact fpIdx_r0 hi
      · cases h

private theorem mem_type {L : Link} {s : MState} {p : Prog} {a : Addr} {r}
    (h : ProgCtx.mem ⟨L, s, p⟩ a = .ok r) : a.type = .MEM := by
  unfold ProgCtx.mem at h
  by_cases ht : a.type = .MEM
  · exact ht
  · simp only [ht, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at h
    cases h

private theorem memP_type {az ez : Int} {sc : Nat} {a : Addr} (ha : a.type = .ADDR) :
    memP az ez sc { a with type := .MEM } = memP az ez sc a := by
  unfold memP
  simp only [ha]
  rfl

private theorem erel_ld {c : Ctx} {e : Eff} {σ : Sym} (hR : ERel c e σ) (a : Ex) (n : Nat) :
    ERel c (e.ld (a.eval c) n) { σ with loads := (a, n) :: σ.loads } :=
  ⟨hR.x, hR.xlt, hR.sp, hR.fl, hR.v, hR.vlt, by simp only [Eff.ld, hR.loads, List.map_cons],
    hR.stores⟩

private theorem fmov_pre {name : String} {n : Nat} {sg : Bool}
    (hm : ProgOp.movMem name = some (n, sg, true)) : pre9 name ∧ (n = 4 ∨ n = 8 ∨ n = 16) := by
  unfold ProgOp.movMem at hm
  split at hm <;> (try cases hm) <;> simp (config := { decide := true }) [pre9]

private theorem fpair_pre {name : String} {ld : Bool} {n : Nat} {sg : Bool}
    (hm : ProgOp.pairOp name = some (ld, n, sg, true)) : pre9 name ∧ (n = 4 ∨ n = 8 ∨ n = 16) := by
  unfold ProgOp.pairOp at hm
  split at hm <;> (try cases hm) <;> simp (config := { decide := true }) [pre9]

private theorem n16 {n : Nat} (hn : n = 4 ∨ n = 8 ∨ n = 16) (h : (n == 16) = false) :
    n = 4 ∨ n = 8 := by
  rcases hn with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr rfl
  · cases h

/-- `FMOVS`/`FMOVD`/`FMOVQ` (`fmovP`): loads (with write-back), `S`/`D` stores and moves,
constants. -/
private theorem fam_fmov {n : Nat} {sg : Bool}
    (hm : ProgOp.movMem p.as.name = some (n, sg, true))
    (h : fmovP az ez n p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e)
    (haz : L.autosize = az) (hez : L.extrasize = ez) :
    Out L p s e σ pc := by
  obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩, hn⟩ := fmov_pre hm
  unfold progEffect at he
  simp only [q1, q2, q3, q4, q5, q6, q7, q8, q9, hm, ↓reduceIte] at he
  unfold fmovP at h
  split at h
  · -- load
    next hf ht =>
    simp only [hf] at he
    obtain ⟨⟨a, wb⟩, hma, h⟩ := pg_bind_ok h
    rw [memP_eval hma hf haz hez, pg_ok_bind] at he
    rcases wb with _ | ⟨r0, b⟩
    · simp only [wbP, Option.map, pg_pure, pg_ok_bind] at h he
      obtain ⟨σ2, hσ2, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨hR, hpc⟩ := wVP_rel (erel_ld (erel_init ⟨s, L.sym⟩) a n) hσ2 he rfl
      exact .inl ⟨hR, hpc⟩
    · simp only [wbP, Option.map] at h he
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨σ2, hσ2, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e1, he1, he⟩ := pg_bind_ok he
      obtain ⟨hR1, -, -, -, hpc1⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1 rfl
      obtain ⟨hR, hpc⟩ := wVP_rel (erel_ld hR1 a n) hσ2 he rfl
      exact .inl ⟨hR, hpc.trans hpc1⟩
  · -- store
    next hf ht =>
    simp only [hf, ht] at he
    obtain ⟨⟨a, wb⟩, hma, h⟩ := pg_bind_ok h
    rw [memP_eval hma ht haz hez, pg_ok_bind] at he
    rcases wb with _ | ⟨r0, b⟩
    · simp only [wbP, Option.map, pg_pure, pg_ok_bind] at h he
      obtain ⟨r, hr, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      simp only [(vP_eval hr).1, pg_ok_bind] at he
      obtain rfl := pg_ok_inj he
      refine .inl ⟨⟨rfl, by simp [Sym.store], rfl, rfl, rfl, by simp [Sym.store], rfl, ?_⟩, rfl⟩
      simp only [Sym.store, List.nil_append, List.map_cons, List.map_nil, vstore_mod hn]
      rfl
    · simp only [wbP, Option.map] at h he
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨r, hr, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e1, he1, he⟩ := pg_bind_ok he
      simp only [(vP_eval hr).1, pg_ok_bind, pg_pure] at he
      obtain rfl := pg_ok_inj he
      obtain ⟨hR1, -, hs1, -, hpc1⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1 rfl
      refine .inl ⟨⟨hR1.x, hR1.xlt, hR1.sp, hR1.fl, hR1.v, hR1.vlt, hR1.loads, ?_⟩, hpc1⟩
      simp only [Sym.store, hR1.stores, hs1, List.nil_append, List.map_cons, List.map_nil,
        vstore_mod hn]
      rfl
  · -- register move
    next hf ht =>
    simp only [hf, ht] at he
    cases h16 : n == 16
    case true => simp only [h16, ↓reduceIte] at h; cases h
    have hn' := n16 hn h16
    simp only [h16, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · next r d hr hd =>
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      simp only [hr, hd, ProgCtx.v, pg_pure, pg_ok_bind] at he
      obtain ⟨hR, hpc⟩ := wVP_rel (erel_init ⟨s, L.sym⟩) hσ1 he (fmov_vv hn' _)
      exact .inl ⟨hR, hpc⟩
    · next r hr hd =>
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      simp only [hr, hd, ProgCtx.v, pg_pure, pg_ok_bind] at he
      obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he (fmov_vx hn' ⟨s, L.sym⟩ r)
      exact .inl ⟨hR, hpc⟩
    · next d hr hd =>
      obtain ⟨x, hx, h⟩ := pg_bind_ok h
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      simp only [hr, hd, (xP_eval hx).1, pg_ok_bind] at he
      obtain ⟨hR, hpc⟩ := wVP_rel (erel_init ⟨s, L.sym⟩) hσ1 he
        ((fmov_xv hn' _).trans (VEx.eval_mkOfX _ _ _).symm)
      exact .inl ⟨hR, hpc⟩
    · cases h
  · -- constant
    next hf ht =>
    simp only [hf, ht] at he
    obtain ⟨k, hk, h⟩ := pg_bind_ok h
    obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    have hk' : ProgOp.fconst (if n == 4 then 0 else 1) p.from_ = .ok k := hk
    rw [hk', pg_ok_bind] at he
    obtain ⟨hR, hpc⟩ := wVP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
    exact .inl ⟨hR, hpc⟩
  · cases h

/-- `FLDPS`/`FLDPD`/`FLDPQ`, `FSTPS`/`FSTPD`/`FSTPQ` (`fpairP`). -/
private theorem fam_fpair {ld : Bool} {n : Nat} {sg : Bool}
    (hp : ProgOp.pairOp p.as.name = some (ld, n, sg, true)) (hm0 : ProgOp.movMem p.as.name = none)
    (h : fpairP az ez ld n p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e)
    (haz : L.autosize = az) (hez : L.extrasize = ez) :
    Out L p s e σ pc := by
  obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩, hn⟩ := fpair_pre hp
  unfold progEffect at he
  simp only [q1, q2, q3, q4, q5, q6, q7, q8, q9, hm0, hp, ↓reduceIte] at he
  unfold fpairP at h
  cases ld <;> simp only [Bool.false_eq_true, Bool.not_false, Bool.not_true, Bool.true_and,
    Bool.false_and, ↓reduceIte] at h he
  · -- store
    by_cases hr : p.from_.type = .REGREG
    case neg => simp only [hr, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at h; cases h
    simp only [hr, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h he
    obtain ⟨⟨a, wb⟩, hma, h⟩ := pg_bind_ok h
    obtain ⟨r', hm', he⟩ := pg_bind_ok he
    rw [memP_eval hma (mem_type hm') haz hez] at hm'
    obtain rfl := pg_ok_inj hm'
    have hst : ∀ (r1 r2 : Nat), ((vStoreEx n r1).eval128 ⟨s, L.sym⟩).toNat % 2 ^ (8 * n) =
        (s.v (BitVec.ofNat 5 r1)).toNat % 2 ^ (8 * n) ∧
        ((vStoreEx n r2).eval128 ⟨s, L.sym⟩).toNat % 2 ^ (8 * n) =
        (s.v (BitVec.ofNat 5 r2)).toNat % 2 ^ (8 * n) :=
      fun r1 r2 => ⟨vstore_mod hn _ r1, vstore_mod hn _ r2⟩
    rcases wb with _ | ⟨r0, b⟩
    · simp only [wbP, Option.map, pg_pure, pg_ok_bind] at h he
      obtain ⟨x1, hx1, h⟩ := pg_bind_ok h
      obtain ⟨x2, hx2, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      simp only [(vP_eval hx1).1, (vP_eval hx2).1, pg_ok_bind] at he
      obtain rfl := pg_ok_inj he
      refine .inl ⟨⟨rfl, by simp [Sym.store], rfl, rfl, rfl, by simp [Sym.store], rfl, ?_⟩, rfl⟩
      simp only [Sym.store, List.nil_append, List.cons_append, List.map_cons, List.map_nil,
        (hst x1 x2).1, (hst x1 x2).2, Ex.eval_mkAdd]
      rfl
    · simp only [wbP, Option.map] at h he
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨x1, hx1, h⟩ := pg_bind_ok h
      obtain ⟨x2, hx2, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e1, he1, he⟩ := pg_bind_ok he
      simp only [(vP_eval hx1).1, (vP_eval hx2).1, pg_ok_bind, pg_pure] at he
      obtain rfl := pg_ok_inj he
      obtain ⟨hR1, -, hs1, -, hpc1⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1 rfl
      refine .inl ⟨⟨hR1.x, hR1.xlt, hR1.sp, hR1.fl, hR1.v, hR1.vlt, hR1.loads, ?_⟩, hpc1⟩
      simp only [Sym.store, hR1.stores, hs1, List.nil_append, List.cons_append, List.map_cons,
        List.map_nil, (hst x1 x2).1, (hst x1 x2).2, Ex.eval_mkAdd]
      rfl
  · -- load
    by_cases hr : p.to.type = .REGREG
    case neg => simp only [hr, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at h; cases h
    simp only [hr, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h he
    obtain ⟨⟨a, wb⟩, hma, h⟩ := pg_bind_ok h
    obtain ⟨r', hm', he⟩ := pg_bind_ok he
    rw [memP_eval hma (mem_type hm') haz hez] at hm'
    obtain rfl := pg_ok_inj hm'
    have hld : ∀ {e1 : Eff} {σ1 : Sym}, ERel ⟨s, L.sym⟩ e1 σ1 →
        ERel ⟨s, L.sym⟩ ((e1.ld (a.eval ⟨s, L.sym⟩) n).ld (a.eval ⟨s, L.sym⟩ + BitVec.ofNat 64 n) n)
          { σ1 with loads := (Ex.mkAdd a (.k (BitVec.ofNat 64 n)), n) :: (a, n) :: σ1.loads } := by
      intro e1 σ1 hR1
      have h2 := erel_ld (erel_ld hR1 a n) (Ex.mkAdd a (.k (BitVec.ofNat 64 n))) n
      rw [Ex.eval_mkAdd] at h2
      exact h2
    have hv2 : (readMem s.mem (a.eval ⟨s, L.sym⟩ + BitVec.ofNat 64 n) n).setWidth 128 =
        (VEx.ld n (Ex.mkAdd a (.k (BitVec.ofNat 64 n)))).eval ⟨s, L.sym⟩ := by
      simp only [VEx.eval, Ex.eval_mkAdd, Ex.eval]
    rcases wb with _ | ⟨r0, b⟩
    · simp only [wbP, Option.map, pg_pure, pg_ok_bind] at h he
      obtain ⟨σ3, hσ3, h⟩ := pg_bind_ok h
      obtain ⟨σ4, hσ4, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e3, he3, he⟩ := pg_bind_ok he
      obtain ⟨hR3, hpc3⟩ := wVP_rel (hld (erel_init ⟨s, L.sym⟩)) hσ3 he3 rfl
      obtain ⟨hR, hpc⟩ := wVP_rel hR3 hσ4 he hv2
      exact .inl ⟨hR, hpc.trans hpc3⟩
    · simp only [wbP, Option.map] at h he
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨σ3, hσ3, h⟩ := pg_bind_ok h
      obtain ⟨σ4, hσ4, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e1, he1, he⟩ := pg_bind_ok he
      obtain ⟨e3, he3, he⟩ := pg_bind_ok he
      obtain ⟨hR1, -, -, -, hpc1⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1 rfl
      obtain ⟨hR3, hpc3⟩ := wVP_rel (hld hR1) hσ3 he3 rfl
      obtain ⟨hR, hpc⟩ := wVP_rel hR3 hσ4 he hv2
      exact .inl ⟨hR, (hpc.trans hpc3).trans hpc1⟩

/-- The `MOV` family: loads (with write-back), stores, register moves, constants, `$addr`. -/
private theorem fam_mov {n : Nat} {sg fp : Bool}
    (hb1 : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] = none)
    (hb2 : ProgOp.baseOf p.as.name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] = none)
    (hb3 : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] = none)
    (hb4 : ProgOp.baseOf p.as.name ["NEG"] = none)
    (hb5 : ProgOp.baseOf p.as.name ["UBFX", "SBFX", "UBFIZ"] = none)
    (hm : ProgOp.movMem p.as.name = some (n, sg, fp))
    (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e)
    (haz : L.autosize = az) (hez : L.extrasize = ez) :
    Out L p s e σ pc := by
  unfold progSymCore at h
  simp only [hb1, hb2, hb3, hb4, hb5, hm] at h
  cases fp
  case true =>
    simp only [↓reduceIte] at h
    exact fam_fmov hm (by simpa only [bind_pure] using h) he haz hez
  obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩, hn⟩ := mov_pre hm
  unfold progEffect at he
  simp only [q1, q2, q3, q4, q5, q6, q7, q8, q9, hm, Bool.false_eq_true, ↓reduceIte] at he
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · -- load
    next hf ht =>
    simp only [hf] at he
    obtain ⟨⟨a, wb⟩, hma, h⟩ := pg_bind_ok h
    rw [memP_eval hma hf haz hez, pg_ok_bind] at he
    have hv : ∀ a : Ex, (if sg = true then ProgOp.sextTo64 n (ProgCtx.load ⟨L, s, p⟩ (a.eval ⟨s, L.sym⟩) n)
        else ProgCtx.load ⟨L, s, p⟩ (a.eval ⟨s, L.sym⟩) n) =
        (if sg = true then Ex.mkSext (8 * n) (Ex.ld n a) else Ex.ld n a).eval ⟨s, L.sym⟩ := by
      intro a; cases sg <;> simp [ProgCtx.load, Ex.eval, Ex.eval_mkSext, ProgOp.sextTo64]
    rcases wb with _ | ⟨r0, b⟩
    · simp only [Option.map, pg_pure, pg_ok_bind] at h he
      obtain ⟨σ2, hσ2, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_ld (erel_init ⟨s, L.sym⟩) a n) hσ2 he (hv a)
      exact .inl ⟨hR, hpc⟩
    · simp only [Option.map] at h he
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨σ2, hσ2, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e1, he1, he⟩ := pg_bind_ok he
      obtain ⟨hR1, -, -, -, hpc1⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1 rfl
      obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_ld hR1 a n) hσ2 he (hv a)
      exact .inl ⟨hR, hpc.trans hpc1⟩
  · -- store
    next hf ht =>
    simp only [hf, ht] at he
    obtain ⟨⟨a, wb⟩, hma, h⟩ := pg_bind_ok h
    rw [memP_eval hma ht haz hez, pg_ok_bind] at he
    rcases wb with _ | ⟨r0, b⟩
    · simp only [Option.map, pg_pure, pg_ok_bind] at h he
      obtain ⟨x, hx, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      simp only [(xP_eval hx).1, pg_ok_bind] at he
      obtain rfl := pg_ok_inj he
      exact .inl ⟨⟨rfl, by simp [Sym.store], rfl, rfl, rfl, by simp [Sym.store], rfl,
        by simp [Sym.store, xP_eval128 hx]⟩, rfl⟩
    · simp only [Option.map] at h he
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨x, hx, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e1, he1, he⟩ := pg_bind_ok he
      simp only [(xP_eval hx).1, pg_ok_bind, pg_pure] at he
      obtain rfl := pg_ok_inj he
      obtain ⟨hR1, -, hs1, -, hpc1⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1 rfl
      refine .inl ⟨⟨hR1.x, hR1.xlt, hR1.sp, hR1.fl, hR1.v, hR1.vlt, hR1.loads, ?_⟩, hpc1⟩
      simp [Sym.store, hR1.stores, hs1, xP_eval128 hx]
  · -- register move
    next hf ht =>
    obtain ⟨x, hx, h⟩ := pg_bind_ok h
    obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    have hx' := xP_eval (L := L) (s := s) (p := p) hx
    simp only [hf, ht, hx'.2.2, wP_fp hσ1, hx'.1, pg_ok_bind] at he
    obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he (by
      rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Ex.eval_mkBfm, Ex.eval_mkTrunc, Ex.eval]
      · simp [ProgOp.maskN]
      · exact sext_bfm 4 (by decide) _
      · exact zext32 _
      · exact sext_bfm 2 (by decide) _
      · exact zext_bfm 2 (by decide) _
      · exact sext_bfm 1 (by decide) _
      · exact zext_bfm 1 (by decide) _)
    exact .inl ⟨hR, hpc⟩
  · -- constant
    next hf ht =>
    simp only [hf, ht] at he
    obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
    exact .inl ⟨hR, hpc⟩
  · -- `$addr`
    next hf ht =>
    simp only [hf, ht] at he
    obtain ⟨⟨a, wb⟩, hma, h⟩ := pg_bind_ok h
    obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    rw [← memP_type hf] at hma
    rw [memP_eval hma rfl haz hez, pg_ok_bind] at he
    simp only at he
    obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
    exact .inl ⟨hR, hpc⟩
  · cases h

/-- A pair load's value: the `n` bytes at `a`, sign-extended when `sg`. -/
private theorem pair_val (L : Link) (s : MState) (p : Prog) (n : Nat) (sg : Bool) (a : Ex) :
    (if sg = true then ProgOp.sextTo64 n (ProgCtx.load ⟨L, s, p⟩ (a.eval ⟨s, L.sym⟩) n)
      else ProgCtx.load ⟨L, s, p⟩ (a.eval ⟨s, L.sym⟩) n) =
      (if sg = true then Ex.mkSext (8 * n) (Ex.ld n a) else Ex.ld n a).eval ⟨s, L.sym⟩ := by
  cases sg <;> simp [ProgCtx.load, Ex.eval, Ex.eval_mkSext, ProgOp.sextTo64]

/-- `LDP`/`STP`/`LDPW`/`STPW`/`LDPSW`. -/
private theorem fam_pair {ld : Bool} {n : Nat} {sg fp : Bool}
    (hb1 : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] = none)
    (hb2 : ProgOp.baseOf p.as.name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] = none)
    (hb3 : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] = none)
    (hb4 : ProgOp.baseOf p.as.name ["NEG"] = none)
    (hb5 : ProgOp.baseOf p.as.name ["UBFX", "SBFX", "UBFIZ"] = none)
    (hm0 : ProgOp.movMem p.as.name = none)
    (hp : ProgOp.pairOp p.as.name = some (ld, n, sg, fp))
    (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e)
    (haz : L.autosize = az) (hez : L.extrasize = ez) :
    Out L p s e σ pc := by
  unfold progSymCore at h
  simp only [hb1, hb2, hb3, hb4, hb5, hm0, hp] at h
  cases fp
  case true =>
    simp only [↓reduceIte] at h
    exact fam_fpair hp hm0 (by simpa only [bind_pure] using h) he haz hez
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := pair_pre hp
  unfold progEffect at he
  simp only [q1, q2, q3, q4, q5, q6, q7, q8, q9, hm0, hp, Bool.false_eq_true, ↓reduceIte] at he
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases ld <;> simp only [Bool.false_eq_true, ↓reduceIte] at h he
  · -- store
    by_cases hr : p.from_.type = .REGREG
    case neg => simp only [hr, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at h; cases h
    simp only [hr, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h he
    obtain ⟨⟨a, wb⟩, hma, h⟩ := pg_bind_ok h
    obtain ⟨r', hm', he⟩ := pg_bind_ok he
    rw [memP_eval hma (mem_type hm') haz hez] at hm'
    obtain rfl := pg_ok_inj hm'
    rcases wb with _ | ⟨r0, b⟩
    · simp only [Option.map, pg_pure, pg_ok_bind] at h he
      obtain ⟨x1, hx1, h⟩ := pg_bind_ok h
      obtain ⟨x2, hx2, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      simp only [(xP_eval hx1).1, (xP_eval hx2).1, pg_ok_bind] at he
      obtain rfl := pg_ok_inj he
      exact .inl ⟨⟨rfl, by simp [Sym.store], rfl, rfl, rfl, by simp [Sym.store], rfl,
        by simp [Sym.store, Ex.eval_mkAdd, Ex.eval, xP_eval128 hx1, xP_eval128 hx2]⟩, rfl⟩
    · simp only [Option.map] at h he
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨x1, hx1, h⟩ := pg_bind_ok h
      obtain ⟨x2, hx2, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e1, he1, he⟩ := pg_bind_ok he
      simp only [(xP_eval hx1).1, (xP_eval hx2).1, pg_ok_bind, pg_pure] at he
      obtain rfl := pg_ok_inj he
      obtain ⟨hR1, -, hs1, -, hpc1⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1 rfl
      refine .inl ⟨⟨hR1.x, hR1.xlt, hR1.sp, hR1.fl, hR1.v, hR1.vlt, hR1.loads, ?_⟩, hpc1⟩
      simp [Sym.store, hR1.stores, hs1, Ex.eval_mkAdd, Ex.eval, xP_eval128 hx1, xP_eval128 hx2]
  · -- load
    by_cases hr : p.to.type = .REGREG
    case neg => simp only [hr, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at h; cases h
    simp only [hr, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h he
    obtain ⟨⟨a, wb⟩, hma, h⟩ := pg_bind_ok h
    obtain ⟨r', hm', he⟩ := pg_bind_ok he
    rw [memP_eval hma (mem_type hm') haz hez] at hm'
    obtain rfl := pg_ok_inj hm'
    have hv2 : (if sg = true then ProgOp.sextTo64 n
          (ProgCtx.load ⟨L, s, p⟩ (a.eval ⟨s, L.sym⟩ + BitVec.ofNat 64 n) n)
        else ProgCtx.load ⟨L, s, p⟩ (a.eval ⟨s, L.sym⟩ + BitVec.ofNat 64 n) n) =
        (if sg = true then Ex.mkSext (8 * n) (Ex.ld n (Ex.mkAdd a (.k (BitVec.ofNat 64 n))))
          else Ex.ld n (Ex.mkAdd a (.k (BitVec.ofNat 64 n)))).eval ⟨s, L.sym⟩ := by
      rw [← pair_val, Ex.eval_mkAdd]; rfl
    have hld : ∀ {e1 : Eff} {σ1 : Sym}, ERel ⟨s, L.sym⟩ e1 σ1 →
        ERel ⟨s, L.sym⟩ ((e1.ld (a.eval ⟨s, L.sym⟩) n).ld (a.eval ⟨s, L.sym⟩ + BitVec.ofNat 64 n) n)
          { σ1 with loads := (Ex.mkAdd a (.k (BitVec.ofNat 64 n)), n) :: (a, n) :: σ1.loads } := by
      intro e1 σ1 hR1
      have h2 := erel_ld (erel_ld hR1 a n) (Ex.mkAdd a (.k (BitVec.ofNat 64 n))) n
      rw [Ex.eval_mkAdd] at h2
      exact h2
    rcases wb with _ | ⟨r0, b⟩
    · simp only [Option.map, pg_pure, pg_ok_bind] at h he
      obtain ⟨σ3, hσ3, h⟩ := pg_bind_ok h
      obtain ⟨σ4, hσ4, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e3, he3, he⟩ := pg_bind_ok he
      obtain ⟨hR3, -, -, -, hpc3⟩ := wP_rel (hld (erel_init ⟨s, L.sym⟩)) hσ3 he3
        (pair_val L s p n sg a)
      obtain ⟨hR, -, -, -, hpc⟩ := wP_rel hR3 hσ4 he hv2
      exact .inl ⟨hR, hpc.trans hpc3⟩
    · simp only [Option.map] at h he
      obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
      obtain ⟨σ3, hσ3, h⟩ := pg_bind_ok h
      obtain ⟨σ4, hσ4, h⟩ := pg_bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
      obtain ⟨e1, he1, he⟩ := pg_bind_ok he
      obtain ⟨e3, he3, he⟩ := pg_bind_ok he
      obtain ⟨hR1, -, -, -, hpc1⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1 rfl
      obtain ⟨hR3, -, -, -, hpc3⟩ := wP_rel (hld hR1) hσ3 he3 (pair_val L s p n sg a)
      obtain ⟨hR, -, -, -, hpc⟩ := wP_rel hR3 hσ4 he hv2
      exact .inl ⟨hR, (hpc.trans hpc3).trans hpc1⟩

/-- `B.cond`. -/
private theorem fam_bcond {k : Nat}
    (hb1 : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] = none)
    (hb2 : ProgOp.baseOf p.as.name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] = none)
    (hb3 : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] = none)
    (hb4 : ProgOp.baseOf p.as.name ["NEG"] = none)
    (hb5 : ProgOp.baseOf p.as.name ["UBFX", "SBFX", "UBFIZ"] = none)
    (hm0 : ProgOp.movMem p.as.name = none) (hp0 : ProgOp.pairOp p.as.name = none)
    (hc : ProgOp.bcond p.as.name = some k)
    (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  unfold progSymCore at h
  simp only [hb1, hb2, hb3, hb4, hb5, hm0, hp0, hc] at h
  obtain ⟨id, hid, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  have key : ∃ t, ProgCtx.target ⟨L, s, p⟩ p.to = .ok t ∧
      e = if s.holds (BitVec.ofNat 4 k) then { pc := some t } else {} := by
    generalize hn : p.as.name = name at hc
    unfold progEffect at he
    unfold ProgOp.bcond at hc
    split at hc <;> cases hc <;>
    · simp (config := { decide := true }) only [hn, ProgOp.baseOf, ProgOp.movMem, ProgOp.pairOp,
        ProgOp.rmw, ProgOp.bcond, ↓reduceIte] at he
      obtain ⟨t, ht, he⟩ := pg_bind_ok he
      exact ⟨t, ht, (pg_ok_inj he).symm⟩
  obtain ⟨t, ht, rfl⟩ := key
  refine .inl ⟨?_, t, targetP_eval hid ht, ?_⟩
  · split <;> exact ⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩
  · simp only [MState.holds]
    split <;> rename_i hh <;> simp only [hh, ↓reduceIte, Bool.false_eq_true]

/-- `CBZ`/`CBNZ`/`CBZW`/`CBNZW`. -/
private theorem fam_cbz {a : Ex} {id : Nat}
    (hn : p.as.name = "CBZ" ∨ p.as.name = "CBNZ" ∨ p.as.name = "CBZW" ∨ p.as.name = "CBNZW")
    (hx : xP p.from_.reg = .ok a) (hid : targetP p.to = .ok id)
    (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e {} (.cbz (!ProgOp.endsS p.as.name "W") (!ProgOp.startsS p.as.name "CBZ") a id) := by
  have key : ∃ t, ProgCtx.target ⟨L, s, p⟩ p.to = .ok t ∧
      e = if (ProgOp.trunc (!ProgOp.endsS p.as.name "W") (a.eval ⟨s, L.sym⟩) == 0) ==
        ProgOp.startsS p.as.name "CBZ" then { pc := some t } else {} := by
    unfold progEffect at he
    rcases hn with hn | hn | hn | hn <;>
    · simp (config := { decide := true }) only [hn, ProgOp.baseOf, ProgOp.movMem, ProgOp.pairOp,
        ProgOp.rmw, ProgOp.bcond, ↓reduceIte, (xP_eval hx).1, pg_ok_bind] at he ⊢
      obtain ⟨t, ht, he⟩ := pg_bind_ok he
      exact ⟨t, ht, (pg_ok_inj he).symm⟩
  obtain ⟨t, ht, rfl⟩ := key
  refine .inl ⟨?_, t, targetP_eval hid ht, ?_⟩
  · split <;> exact ⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩
  · cases ProgOp.trunc (!ProgOp.endsS p.as.name "W") (a.eval ⟨s, L.sym⟩) == 0 <;>
      cases ProgOp.startsS p.as.name "CBZ" <;> rfl

/-- `TBZ`/`TBNZ`. -/
private theorem fam_tbz {a : Ex} {id : Nat} (hn : p.as.name = "TBZ" ∨ p.as.name = "TBNZ")
    (hx : xP p.reg = .ok a) (hid : targetP p.to = .ok id)
    (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e {} (.tbz (p.as.name == "TBNZ") p.from_.offset.toNat a id) := by
  have key : ∃ t, ProgCtx.target ⟨L, s, p⟩ p.to = .ok t ∧
      e = if (a.eval ⟨s, L.sym⟩).getLsbD p.from_.offset.toNat == (p.as.name == "TBNZ")
        then { pc := some t } else {} := by
    unfold progEffect at he
    rcases hn with hn | hn <;>
    · simp (config := { decide := true }) only [hn, ProgOp.baseOf, ProgOp.movMem, ProgOp.pairOp,
        ProgOp.rmw, ProgOp.bcond, ↓reduceIte, (xP_eval hx).1, pg_ok_bind] at he ⊢
      obtain ⟨t, ht, he⟩ := pg_bind_ok he
      exact ⟨t, ht, (pg_ok_inj he).symm⟩
  obtain ⟨t, ht, rfl⟩ := key
  refine .inl ⟨?_, t, targetP_eval hid ht, ?_⟩
  · split <;> exact ⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩
  · split <;> rfl

private theorem target_sym {L : Link} {s : MState} {p : Prog} {a : Addr} {n : Nat}
    (ht : a.type = .BRANCH) (hv : ∀ id, a.val = .target id → False) (hs : a.sym = some n) :
    ProgCtx.target ⟨L, s, p⟩ a = .ok (L.sym n + BitVec.ofInt 64 a.offset) := by
  unfold ProgCtx.target
  rw [ht, hs]
  cases hval : a.val <;> first | exact (hv _ hval).elim | rfl

private theorem fall_ok {L : Link} {s : MState} {p : Prog} {f : BitVec 64}
    (h : ProgCtx.fall ⟨L, s, p⟩ = .ok f) : L.nextAddr p.id = some f := by
  unfold ProgCtx.fall at h
  split at h
  · rename_i a ha; cases h; exact ha
  · cases h

private theorem wX_30 (f : BitVec 64) : ({} : Eff).wX (REG_R0 + 30) f = .ok { x := [(30, f)] } := by
  rfl

/-! ### Multiplies, data processing (1 source), conditional selects, ordered accesses -/

private theorem mul_pre {name op : String} {sf : Bool}
    (hb : ProgOp.baseOf name ["MUL", "MNEG", "MADD", "MSUB", "UMULH", "SMULH"] = some (op, sf)) :
    (op ∈ ["MUL", "MNEG", "UMULH", "SMULH"] ∧ ProgOp.baseOf name ProgOp.binNames = some (op, sf)) ∨
    (op ∈ ["MADD", "MSUB"] ∧ ProgOp.baseOf name ProgOp.binNames = none ∧
      ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
      ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
      ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
      ProgOp.baseOf name ["MADD", "MSUB"] = some (op, sf)) := by
  obtain ⟨hop, rfl⟩ := baseOf_some hb
  have key : ∀ op ∈ ["MUL", "MNEG", "MADD", "MSUB", "UMULH", "SMULH"], ∀ sf : Bool,
      (op ∈ ["MUL", "MNEG", "UMULH", "SMULH"] ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = some (op, sf)) ∨
      (op ∈ ["MADD", "MSUB"] ∧ ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = none ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ["CMP", "CMN", "TST"] = none ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ["MADD", "MSUB"] = some (op, sf)) := by
    decide
  exact key op hop sf

private theorem mul_val (sf : Bool) (x y : BitVec 64) :
    (sized sf fun _ e => e (ProgOp.trunc sf x) * e (ProgOp.trunc sf y)) = dp3Op sf 0 false 0 x y := by
  cases sf <;> simp [dp3Op, sized, ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

private theorem mneg_val (sf : Bool) (x y : BitVec 64) :
    (sized sf fun _ e => -(e (ProgOp.trunc sf x) * e (ProgOp.trunc sf y))) =
      dp3Op sf 0 true 0 x y := by
  cases sf <;> simp [dp3Op, sized, ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

/-- `MUL`/`MNEG`/`UMULH`/`SMULH` (`binOp`). -/
private theorem fam_mulb {op : String} {sf : Bool} (hop : op ∈ ["MUL", "MNEG", "UMULH", "SMULH"])
    (hbin : ProgOp.baseOf p.as.name ProgOp.binNames = some (op, sf))
    (hm : mulP op sf p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  have hnsh : ["LSL", "LSR", "ASR", "ROR"].contains op = false := by
    have key : ∀ op ∈ ["MUL", "MNEG", "UMULH", "SMULH"],
        ["LSL", "LSR", "ASR", "ROR"].contains op = false := by decide
    exact key op hop
  unfold progEffect at he
  simp only [hbin, ProgCtx.rn, hnsh, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at he
  unfold mulP at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl
  · simp (config := { decide := true }) only [bind_assoc, pure_bind] at hm
    obtain ⟨x, hx, hm⟩ := pg_bind_ok hm
    obtain ⟨y, hy, hm⟩ := pg_bind_ok hm
    obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
    simp (config := { decide := true }) only [src_reg hx, srcP_eval hy, pg_ok_bind, ProgOp.binOp] at he
    obtain ⟨e1, he1, he⟩ := pg_bind_ok he
    obtain rfl := pg_ok_inj he
    obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
      (by rw [Ex.eval_mkDp3]; exact mul_val sf _ _)
    exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩
  · simp (config := { decide := true }) only [bind_assoc, pure_bind] at hm
    obtain ⟨x, hx, hm⟩ := pg_bind_ok hm
    obtain ⟨y, hy, hm⟩ := pg_bind_ok hm
    obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
    simp (config := { decide := true }) only [src_reg hx, srcP_eval hy, pg_ok_bind, ProgOp.binOp] at he
    obtain ⟨e1, he1, he⟩ := pg_bind_ok he
    obtain rfl := pg_ok_inj he
    obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
      (by rw [Ex.eval_mkDp3]; exact mneg_val sf _ _)
    exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩
  all_goals
    cases sf
    · simp (config := { decide := true }) only [Bool.not_false, ↓reduceIte] at hm
      obtain ⟨r, hr, -⟩ := pg_bind_ok hm
      cases hr
    simp (config := { decide := true }) only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind_assoc, pure_bind] at hm
    obtain ⟨x, hx, hm⟩ := pg_bind_ok hm
    obtain ⟨y, hy, hm⟩ := pg_bind_ok hm
    obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
    simp (config := { decide := true }) only [src_reg hx, srcP_eval hy, pg_ok_bind, ProgOp.binOp] at he
    obtain ⟨e1, he1, he⟩ := pg_bind_ok he
    obtain rfl := pg_ok_inj he
    obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
      (by rw [Ex.eval_mkDp3]; rfl)
    exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩

/-- `MADD`/`MSUB` (and `W`). -/
private theorem fam_madd {op : String} {sf : Bool} (hop : op ∈ ["MADD", "MSUB"])
    (q1 : ProgOp.baseOf p.as.name ProgOp.binNames = none)
    (q2 : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] = none)
    (q3 : ProgOp.baseOf p.as.name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none)
    (q4 : ProgOp.baseOf p.as.name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none)
    (q5 : ProgOp.baseOf p.as.name ["MADD", "MSUB"] = some (op, sf))
    (hm : mulP op sf p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  unfold progEffect at he
  simp only [q1, q2, q3, q4, q5, ProgCtx.rest] at he
  unfold mulP restP at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  cases hrest : p.rest[0]? with
  | none =>
    rcases hop with rfl | rfl <;>
    · simp (config := { decide := true }) only [hrest, bind_assoc, pure_bind] at hm
      obtain ⟨m, -, hm⟩ := pg_bind_ok hm
      obtain ⟨a, -, hm⟩ := pg_bind_ok hm
      obtain ⟨q, hq, -⟩ := pg_bind_ok hm
      cases hq
  | some q =>
    simp only [hrest, pg_pure, pg_ok_bind] at he
    rcases hop with rfl | rfl <;>
    · simp (config := { decide := true }) only [hrest, bind_assoc, pure_bind] at hm
      obtain ⟨m, hmx, hm⟩ := pg_bind_ok hm
      obtain ⟨a, hax, hm⟩ := pg_bind_ok hm
      obtain ⟨n, hnx, hm⟩ := pg_bind_ok hm
      obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
      simp only [(xP_eval hmx).1, (xP_eval hax).1, (xP_eval hnx).1, pg_ok_bind] at he
      obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he (by rw [Ex.eval_mkDp3])
      exact .inl ⟨hR, hpc⟩

private theorem dp1_pre {name op : String} {sf : Bool}
    (hb : ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = some (op, sf)) :
    ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
      ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none := by
  obtain ⟨hop, rfl⟩ := baseOf_some hb
  have key : ∀ op ∈ ["CLZ", "RBIT", "REV", "REV16", "REV32"], ∀ sf : Bool,
      ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["CMP", "CMN", "TST"] = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none := by
    decide
  exact key op hop sf

/-- `CLZ`/`RBIT`/`REV`/`REV16`/`REV32` (and `W`). -/
private theorem fam_dp1 {op : String} {sf : Bool}
    (hb : ProgOp.baseOf p.as.name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = some (op, sf))
    (hm : dp1P op sf p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  obtain ⟨hop, -⟩ := baseOf_some hb
  obtain ⟨q1, q2, q3⟩ := dp1_pre hb
  unfold progEffect at he
  simp only [q1, q2, q3, hb] at he
  unfold dp1P at hm
  obtain ⟨x, hx, hm⟩ := pg_bind_ok hm
  obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
  rw [(xP_eval hx).1, pg_ok_bind] at he
  obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl <;> rfl)
  exact .inl ⟨hR, hpc⟩

private theorem csel_pre {name op : String} {sf : Bool}
    (hb : ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG", "CSET", "CSETM"] = some (op, sf)) :
    ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
    ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
    ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
    ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
    ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = none ∧
    ProgOp.baseOf name ["EXTR"] = none ∧
    ((op ∈ ["CSEL", "CSINC", "CSINV", "CSNEG"] ∧
      ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = some (op, sf)) ∨
     (op ∈ ["CSET", "CSETM"] ∧ ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
      ProgOp.baseOf name ["CSET", "CSETM"] = some (op, sf))) := by
  obtain ⟨hop, rfl⟩ := baseOf_some hb
  have key : ∀ op ∈ ["CSEL", "CSINC", "CSINV", "CSNEG", "CSET", "CSETM"], ∀ sf : Bool,
      ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["CMP", "CMN", "TST"] = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["MADD", "MSUB"] = none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] =
        none ∧
      ProgOp.baseOf (if sf then op else op ++ "W") ["EXTR"] = none ∧
      ((op ∈ ["CSEL", "CSINC", "CSINV", "CSNEG"] ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ["CSEL", "CSINC", "CSINV", "CSNEG"] = some (op, sf)) ∨
       (op ∈ ["CSET", "CSETM"] ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ["CSET", "CSETM"] = some (op, sf))) := by
    decide
  exact key op hop sf

/-- Inverting the low bit of a condition other than `AL`/`NV` negates it. -/
private theorem holds_inv {c : BitVec 4} (hc : c.toNat < 14) (f : GoFV.SSA.Sem.Flags) :
    (condOf (c ^^^ 1)).holds f = !(condOf c).holds f := by
  have key : ∀ k : Fin 16, k.val < 14 → ∀ n z cf v : Bool,
      (condOf (BitVec.ofFin k ^^^ 1)).holds ⟨n, z, cf, v⟩ =
        !(condOf (BitVec.ofFin k)).holds ⟨n, z, cf, v⟩ := by decide
  obtain ⟨n, z, cf, v⟩ := f
  exact key c.toFin hc n z cf v

private theorem csel_v (sf h : Bool) (n m : BitVec 64) :
    (if h then ProgOp.trunc sf n else ProgOp.trunc sf m) = cselVal sf false false h n m := by
  cases h <;> cases sf <;> simp [cselVal, sized, ProgOp.trunc]

private theorem csinc_v (sf h : Bool) (n m : BitVec 64) :
    (if h then ProgOp.trunc sf n else ProgOp.trunc sf (ProgOp.trunc sf m + 1)) =
      cselVal sf false true h n m := by
  cases h <;> cases sf <;> simp [cselVal, sized, ProgOp.trunc] <;> bv_omega

private theorem csinv_v (sf h : Bool) (n m : BitVec 64) :
    (if h then ProgOp.trunc sf n else ProgOp.trunc sf (~~~(ProgOp.trunc sf m))) =
      cselVal sf true false h n m := by
  cases h <;> cases sf <;> simp [cselVal, sized, ProgOp.trunc] <;> bv_omega

private theorem csneg_v (sf h : Bool) (n m : BitVec 64) :
    (if h then ProgOp.trunc sf n else ProgOp.trunc sf (-(ProgOp.trunc sf m))) =
      cselVal sf true true h n m := by
  cases h <;> cases sf <;> simp [cselVal, sized, ProgOp.trunc] <;> bv_omega

private theorem cset_v (sf h : Bool) :
    (if h then (1 : BitVec 64) else 0) = cselVal sf false true (!h) 0 0 := by
  cases h <;> cases sf <;> decide

private theorem csetm_v (sf h : Bool) :
    (if h then ProgOp.trunc sf (-1) else 0) = cselVal sf true false (!h) 0 0 := by
  cases h <;> cases sf <;> decide

/-- The register write of a conditional select. -/
private theorem csel_tail {r : Ex} {val : BitVec 64} {σ1 : Sym}
    (hσ1 : wP {} p.to.reg r = .ok σ1) (he : ({} : Eff).wX p.to.reg val = .ok e)
    (hv : val = r.eval ⟨s, L.sym⟩) : Out L p s e σ1 .fall := by
  obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he hv
  exact .inl ⟨hR, hpc⟩

/-- `CSEL`/`CSINC`/`CSINV`/`CSNEG`/`CSET`/`CSETM` (and `W`). -/
private theorem fam_csel {op : String} {sf : Bool}
    (hb : ProgOp.baseOf p.as.name ["CSEL", "CSINC", "CSINV", "CSNEG", "CSET", "CSETM"] = some (op, sf))
    (hm : cselP op sf p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, hsel⟩ := csel_pre hb
  unfold progEffect at he
  simp only [q1, q2, q3, q4, q5, q6, q7] at he
  unfold cselP restP at hm
  obtain ⟨cc, hcc, hm⟩ := pg_bind_ok hm
  rcases hsel with ⟨hop, hs⟩ | ⟨hop, hs0, hs⟩
  · simp only [hs, hcc, pg_ok_bind, ProgCtx.rest] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    cases hrest : p.rest[0]? with
    | none =>
      rcases hop with rfl | rfl | rfl | rfl <;>
      · simp (config := { decide := true }) only [hrest, bind_assoc, pure_bind] at hm
        obtain ⟨n, -, hm⟩ := pg_bind_ok hm
        obtain ⟨q, hq, -⟩ := pg_bind_ok hm
        cases hq
    | some q =>
      simp only [hrest, pg_pure, pg_ok_bind] at he
      rcases hop with rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) only [hrest, bind_assoc, pure_bind] at hm <;>
        obtain ⟨n, hnx, hm⟩ := pg_bind_ok hm <;>
        obtain ⟨m, hmx, hm⟩ := pg_bind_ok hm <;>
        obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm <;>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm) <;>
        simp only [(xP_eval hnx).1, (xP_eval hmx).1, pg_ok_bind] at he
      · exact csel_tail hσ1 he (by simp only [Ex.eval]; exact csel_v sf _ _ _)
      · exact csel_tail hσ1 he (by simp only [Ex.eval]; exact csinc_v sf _ _ _)
      · exact csel_tail hσ1 he (by simp only [Ex.eval]; exact csinv_v sf _ _ _)
      · exact csel_tail hσ1 he (by simp only [Ex.eval]; exact csneg_v sf _ _ _)
  · simp only [hs0, hs, hcc, pg_ok_bind] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    by_cases h14 : cc.toNat ≥ 14
    · rcases hop with rfl | rfl <;>
      · simp (config := { decide := true }) only [h14, ↓reduceIte] at hm
        obtain ⟨r, hr, -⟩ := pg_bind_ok hm
        cases hr
    have hinv := holds_inv (c := cc) (by omega)
    rcases hop with rfl | rfl <;>
      simp (config := { decide := true }) only [h14, ↓reduceIte, bind_assoc, pure_bind] at hm <;>
      obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm <;>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
    · have e1 : ("CSET" == "CSETM") = false := by decide
      exact csel_tail hσ1 he (by
        simp only [Ex.eval, beq_self_eq_true, e1, ↓reduceIte]; rw [hinv]; exact cset_v sf _)
    · have e1 : ("CSETM" == "CSET") = false := by decide
      exact csel_tail hσ1 he (by
        simp only [Ex.eval, beq_self_eq_true, e1, Bool.false_eq_true, ↓reduceIte]; rw [hinv]
        exact csetm_v sf _)

private theorem excl_names {name : String} {ld : Bool} {n : Nat} (h : exclOp name = some (ld, n)) :
    (name = "LDAR" ∧ ld = true ∧ n = 8) ∨ (name = "LDARW" ∧ ld = true ∧ n = 4) ∨
    (name = "LDARH" ∧ ld = true ∧ n = 2) ∨ (name = "LDARB" ∧ ld = true ∧ n = 1) ∨
    (name = "STLR" ∧ ld = false ∧ n = 8) ∨ (name = "STLRW" ∧ ld = false ∧ n = 4) ∨
    (name = "STLRH" ∧ ld = false ∧ n = 2) ∨ (name = "STLRB" ∧ ld = false ∧ n = 1) := by
  unfold exclOp at h
  split at h <;> cases h <;> simp

set_option hygiene false in
/-- A load `exclP` accepts (`hm`), `progEffect` reduced to its `LDAR` branch (`he`). -/
local macro "excl_ld_tac" : tactic => `(tactic| (
  simp only [↓reduceIte] at hm
  by_cases hf : p.from_.type = .MEM
  case neg => simp only [bne_iff_ne, ne_eq, hf, not_false_eq_true, ↓reduceIte] at hm; cases hm
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hm
  obtain ⟨⟨a, wb⟩, hma, hm⟩ := pg_bind_ok hm
  obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
  rw [memP_eval hma hf haz hez, pg_ok_bind] at he
  obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_ld (erel_init ⟨s, L.sym⟩) a _) hσ1 he rfl
  exact .inl ⟨hR, hpc⟩))

set_option hygiene false in
/-- A store `exclP` accepts (`hm`), `progEffect` reduced to its `STLR` branch (`he`). -/
local macro "excl_st_tac" : tactic => `(tactic| (
  simp only [Bool.false_eq_true, ↓reduceIte] at hm
  by_cases ht : p.to.type = .MEM
  case neg => simp only [bne_iff_ne, ne_eq, ht, not_false_eq_true, ↓reduceIte] at hm; cases hm
  simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hm
  obtain ⟨⟨a, wb⟩, hma, hm⟩ := pg_bind_ok hm
  obtain ⟨x, hx, hm⟩ := pg_bind_ok hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
  rw [memP_eval hma ht haz hez, pg_ok_bind] at he
  simp only [(xP_eval hx).1, pg_ok_bind, pg_pure] at he
  obtain rfl := pg_ok_inj he
  exact .inl ⟨⟨rfl, by simp [Sym.store], rfl, rfl, rfl, by simp [Sym.store], rfl,
    by simp [Sym.store, xP_eval128 hx]⟩, rfl⟩))

/-- `LDAR*`/`STLR*` (`exclOp`). -/
private theorem fam_excl {az ez : Int} {ld : Bool} {n : Nat} (haz : L.autosize = az)
    (hez : L.extrasize = ez) (hx : exclOp p.as.name = some (ld, n))
    (hm : exclP az ez ld n p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  unfold progEffect at he
  unfold exclP at hm
  rcases excl_names hx with ⟨hn, rfl, rfl⟩ | ⟨hn, rfl, rfl⟩ | ⟨hn, rfl, rfl⟩ | ⟨hn, rfl, rfl⟩ |
      ⟨hn, rfl, rfl⟩ | ⟨hn, rfl, rfl⟩ | ⟨hn, rfl, rfl⟩ | ⟨hn, rfl, rfl⟩
  all_goals
    simp (config := { decide := true }) only [hn, ProgOp.baseOf, ProgOp.movMem, ProgOp.pairOp,
      ProgOp.suffixBytes, ↓reduceIte] at he
  · excl_ld_tac
  · excl_ld_tac
  · excl_ld_tac
  · excl_ld_tac
  · excl_st_tac
  · excl_st_tac
  · excl_st_tac
  · excl_st_tac

/-! ### Variable shifts, divisions, remainders, inverted logical operations (`dp2P`) -/

private theorem dp2_pre {name op : String} {sf : Bool}
    (hb : ProgOp.baseOf name ["ROR", "UDIV", "SDIV", "REM", "UREM", "BIC", "ORN", "EON", "MVN"] =
      some (op, sf)) :
    (op ∈ ["ROR", "UDIV", "SDIV"] ∧ ProgOp.baseOf name ProgOp.binNames = some (op, sf)) ∨
    (op ∈ ["REM", "UREM"] ∧ ProgOp.baseOf name ProgOp.binNames = some (op, sf)) ∨
    (op ∈ ["BIC", "ORN", "EON"] ∧ ProgOp.baseOf name ProgOp.binNames = some (op, sf)) ∨
    (op = "MVN" ∧ ProgOp.baseOf name ProgOp.binNames = none ∧
      ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
      ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = some (op, sf)) := by
  obtain ⟨hop, rfl⟩ := baseOf_some hb
  have key : ∀ op ∈ ["ROR", "UDIV", "SDIV", "REM", "UREM", "BIC", "ORN", "EON", "MVN"], ∀ sf : Bool,
      (op ∈ ["ROR", "UDIV", "SDIV"] ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = some (op, sf)) ∨
      (op ∈ ["REM", "UREM"] ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = some (op, sf)) ∨
      (op ∈ ["BIC", "ORN", "EON"] ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = some (op, sf)) ∨
      (op = "MVN" ∧ ProgOp.baseOf (if sf then op else op ++ "W") ProgOp.binNames = none ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ["CMP", "CMN", "TST"] = none ∧
        ProgOp.baseOf (if sf then op else op ++ "W") ["NEG", "NEGS", "MVN", "NGC", "NGCS"] =
          some (op, sf)) := by
    decide
  exact key op hop sf

/-- `REM`/`UREM` at the datasize: the division into `REGTMP`, then `MSUB`. -/
private theorem rem_val (sf : Bool) (x y : BitVec 64) :
    (sized sf fun _ e => GoFV.SSA.Sem.Arm64.srem (e (ProgOp.trunc sf x)) (e (ProgOp.trunc sf y))) =
      dp3Op sf 0 true x (dp2Op sf 3 x y) y := by
  cases sf <;> simp [dp3Op, dp2Op, sized, ProgOp.trunc, GoFV.SSA.Sem.Arm64.srem,
    BitVec.setWidth_setWidth_of_le]

private theorem urem_val (sf : Bool) (x y : BitVec 64) :
    (sized sf fun _ e => GoFV.SSA.Sem.Arm64.urem (e (ProgOp.trunc sf x)) (e (ProgOp.trunc sf y))) =
      dp3Op sf 0 true x (dp2Op sf 2 x y) y := by
  cases sf <;> simp [dp3Op, dp2Op, sized, ProgOp.trunc, GoFV.SSA.Sem.Arm64.urem,
    BitVec.setWidth_setWidth_of_le]

/-- `binOp`'s inverted operand (`BIC`/`ORN`/`EON`) is `Ex.inv`'s. -/
private theorem bic_val (sf : Bool) (opc : BitVec 2) (x y : BitVec 64) :
    logical sf opc (ProgOp.trunc sf x) (ProgOp.trunc sf (~~~(ProgOp.trunc sf y))) =
      logical sf opc x (sized sf fun _ e => ~~~(e y)) := by
  cases sf <;> simp [logical, sizedF, sized, ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

private theorem mvn_val (sf : Bool) (opc : BitVec 2) (x y : BitVec 64) :
    logical sf opc x (ProgOp.trunc sf (~~~(ProgOp.trunc sf y))) =
      logical sf opc x (sized sf fun _ e => ~~~(e y)) := by
  cases sf <;> simp [logical, sizedF, sized, ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

/-- `ROR` by a register, `UDIV`/`SDIV` (and `W`): data-processing (2 source). -/
private theorem fam_div {op : String} {sf : Bool} (hop : op ∈ ["ROR", "UDIV", "SDIV"])
    (hbin : ProgOp.baseOf p.as.name ProgOp.binNames = some (op, sf))
    (hm : dp2P op sf p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  unfold progEffect at he
  simp only [hbin, ProgCtx.rn] at he
  unfold dp2P at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  by_cases hc : p.from_.type = .CONST
  · rcases hop with rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [hc, beq_self_eq_true, ↓reduceIte] at hm <;>
    cases hm
  have hc' : (p.from_.type == .CONST) = false := by simpa using hc
  simp only [hc', Bool.false_and, Bool.false_eq_true, ↓reduceIte] at he
  rcases hop with rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [hc', Bool.false_eq_true, ↓reduceIte, bind_assoc,
      pure_bind] at hm
    obtain ⟨x, hx, hm⟩ := pg_bind_ok hm
    obtain ⟨y, hy, hm⟩ := pg_bind_ok hm
    obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
    simp (config := { decide := true }) only [src_reg hx, srcP_eval hy, pg_ok_bind,
      ProgOp.binOp] at he
    obtain ⟨e1, he1, he⟩ := pg_bind_ok he
    obtain rfl := pg_ok_inj he
    obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
      (by rw [Ex.eval_mkDp2, dp2_trunc])
    exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩

/-- `REM`/`UREM` (and `W`): the division into `REGTMP` and `MSUB`. -/
private theorem fam_rem {op : String} {sf : Bool} (hop : op ∈ ["REM", "UREM"])
    (hbin : ProgOp.baseOf p.as.name ProgOp.binNames = some (op, sf))
    (hm : dp2P op sf p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  have hnsh : ["LSL", "LSR", "ASR", "ROR"].contains op = false := by
    have key : ∀ op ∈ ["REM", "UREM"], ["LSL", "LSR", "ASR", "ROR"].contains op = false := by decide
    exact key op hop
  unfold progEffect at he
  simp only [hbin, ProgCtx.rn, hnsh, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at he
  unfold dp2P at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  all_goals
    simp (config := { decide := true }) only [bind_assoc, pure_bind, ↓reduceIte] at hm
    obtain ⟨x, hx, hm⟩ := pg_bind_ok hm
    obtain ⟨y, hy, hm⟩ := pg_bind_ok hm
    obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
    simp (config := { decide := true }) only [src_reg hx, srcP_eval hy, pg_ok_bind, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, ProgOp.binOp] at he
    obtain ⟨e1, he1, he⟩ := pg_bind_ok he
    obtain rfl := pg_ok_inj he
  · obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
      (by rw [Ex.eval_mkDp3, Ex.eval_mkDp2]; exact rem_val sf _ _)
    exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩
  · obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
      (by rw [Ex.eval_mkDp3, Ex.eval_mkDp2]; exact urem_val sf _ _)
    exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩

/-- `BIC`/`ORN`/`EON` (and `W`): the logical operation of the inverted operand. -/
private theorem fam_bic {op : String} {sf : Bool} (hop : op ∈ ["BIC", "ORN", "EON"])
    (hbin : ProgOp.baseOf p.as.name ProgOp.binNames = some (op, sf))
    (hm : dp2P op sf p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  have hnsh : ["LSL", "LSR", "ASR", "ROR"].contains op = false := by
    have key : ∀ op ∈ ["BIC", "ORN", "EON"], ["LSL", "LSR", "ASR", "ROR"].contains op = false := by
      decide
    exact key op hop
  unfold progEffect at he
  simp only [hbin, ProgCtx.rn, hnsh, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at he
  unfold dp2P at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [bind_assoc, pure_bind, ↓reduceIte] at hm
    obtain ⟨x, hx, hm⟩ := pg_bind_ok hm
    obtain ⟨y, hy, hm⟩ := pg_bind_ok hm
    obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
    simp (config := { decide := true }) only [src_reg hx, srcP_eval hy, pg_ok_bind, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, ProgOp.binOp] at he
    obtain ⟨e1, he1, he⟩ := pg_bind_ok he
    obtain rfl := pg_ok_inj he
    obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
      (by rw [Ex.eval_mkLogical, Ex.eval_mkInv, bic_val])
    exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩

/-- `MVN` (and `W`): `ORN` with `ZR`. -/
private theorem fam_mvn {sf : Bool}
    (q1 : ProgOp.baseOf p.as.name ProgOp.binNames = none)
    (q2 : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] = none)
    (q3 : ProgOp.baseOf p.as.name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = some ("MVN", sf))
    (hm : dp2P "MVN" sf p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  unfold progEffect at he
  simp only [q1, q2, q3] at he
  unfold dp2P at hm
  simp (config := { decide := true }) only [bind_assoc, pure_bind] at hm
  obtain ⟨y, hy, hm⟩ := pg_bind_ok hm
  obtain ⟨σ1, hσ1, hm⟩ := pg_bind_ok hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj hm)
  simp (config := { decide := true }) only [srcP_eval hy, pg_ok_bind, ProgOp.binOp] at he
  obtain ⟨e1, he1, he⟩ := pg_bind_ok he
  obtain rfl := pg_ok_inj he
  obtain ⟨hR, -, -, hfl, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he1
    (by rw [Ex.eval_mkLogical, Ex.eval_mkInv, mvn_val]; rfl)
  exact .inl ⟨⟨hR.x, hR.xlt, hR.sp, by rw [hfl]; rfl, hR.v, hR.vlt, hR.loads, hR.stores⟩, hpc⟩

private theorem fam_dp2 {op : String} {sf : Bool}
    (hb : ProgOp.baseOf p.as.name
      ["ROR", "UDIV", "SDIV", "REM", "UREM", "BIC", "ORN", "EON", "MVN"] = some (op, sf))
    (hm : dp2P op sf p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  rcases dp2_pre hb with ⟨hop, hbin⟩ | ⟨hop, hbin⟩ | ⟨hop, hbin⟩ | ⟨rfl, q1, q2, q3⟩
  · exact fam_div hop hbin hm he
  · exact fam_rem hop hbin hm he
  · exact fam_bic hop hbin hm he
  · exact fam_mvn q1 q2 q3 hm he

/-! ### SIMD&FP data processing (`fpOp?`, `fpP`)

One lemma per `FpOp` form, `progEffect`'s branch given with its fields as it computes them from
the name (`ft'`, `opc'`, …), equal to `fpOp?`'s (`fam_fp` decides the equalities per name). -/

private theorem fp_fp1 {ft ft' : BitVec 2} {opc opc' : BitVec 6}
    (h : fpP (.fp1 ft opc) p = .ok (σ, pc))
    (he : (do
      let x ← ProgCtx.v ⟨L, s, p⟩ p.from_.reg
      ({} : Eff).wV p.to.reg (fp1Op ft' opc' x)) = .ok e)
    (h1 : ft' = ft) (h2 : opc' = opc) : Out L p s e σ pc := by
  subst h1 h2
  simp only [fpP] at h
  obtain ⟨a, ha, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  rw [(vP_eval ha).1, pg_ok_bind] at he
  obtain ⟨hR, hpc⟩ := wVP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
  exact .inl ⟨hR, hpc⟩

private theorem fp_fp2 {ft ft' : BitVec 2} {opc opc' : BitVec 4}
    (h : fpP (.fp2 ft opc) p = .ok (σ, pc))
    (he : (do
      let x ← ProgCtx.v ⟨L, s, p⟩ (ProgCtx.rn ⟨L, s, p⟩)
      let y ← ProgCtx.v ⟨L, s, p⟩ p.from_.reg
      ({} : Eff).wV p.to.reg (fp2Op ft' opc' x y)) = .ok e)
    (h1 : ft' = ft) (h2 : opc' = opc) : Out L p s e σ pc := by
  subst h1 h2
  simp only [fpP] at h
  obtain ⟨a, ha, h⟩ := pg_bind_ok h
  obtain ⟨b, hb, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  have hrn : ProgCtx.rn ⟨L, s, p⟩ = (if p.reg != 0 then p.reg else p.to.reg) := rfl
  rw [hrn, (vP_eval ha).1, pg_ok_bind, (vP_eval hb).1, pg_ok_bind] at he
  obtain ⟨hR, hpc⟩ := wVP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
  exact .inl ⟨hR, hpc⟩

private theorem fp_fp3 {ft ft' : BitVec 2} {o1 o1' o0 o0' : Bool}
    (h : fpP (.fp3 ft o1 o0) p = .ok (σ, pc))
    (he : (do
      let a ← ProgCtx.v ⟨L, s, p⟩ p.reg
      let q ← ProgCtx.rest ⟨L, s, p⟩ 0
      let n ← ProgCtx.v ⟨L, s, p⟩ q.reg
      let m ← ProgCtx.v ⟨L, s, p⟩ p.from_.reg
      ({} : Eff).wV p.to.reg (fp3Op ft' o1' o0' a n m)) = .ok e)
    (h1 : ft' = ft) (h2 : o1' = o1) (h3 : o0' = o0) : Out L p s e σ pc := by
  subst h1 h2 h3
  simp only [fpP] at h
  obtain ⟨a, ha, h⟩ := pg_bind_ok h
  obtain ⟨q, hq, h⟩ := pg_bind_ok h
  obtain ⟨n, hn, h⟩ := pg_bind_ok h
  obtain ⟨m, hm, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  have hq' : ProgCtx.rest ⟨L, s, p⟩ 0 = .ok q := hq
  rw [(vP_eval ha).1, pg_ok_bind, hq', pg_ok_bind, (vP_eval hn).1, pg_ok_bind, (vP_eval hm).1,
    pg_ok_bind] at he
  obtain ⟨hR, hpc⟩ := wVP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
  exact .inl ⟨hR, hpc⟩

private theorem fp_cmp {ft ft' : BitVec 2}
    (h : fpP (.cmp ft) p = .ok (σ, pc))
    (he : (if (p.from_.type == AddrType.FCONST) = true then do
          let y ← (pure 0 : Except String (BitVec 128))
          let a ← ProgCtx.v ⟨L, s, p⟩ p.reg
          pure ({ flags := some (fcmpOp ft' a y) } : Eff)
        else do
          let y ← ProgCtx.v ⟨L, s, p⟩ p.from_.reg
          let a ← ProgCtx.v ⟨L, s, p⟩ p.reg
          pure ({ flags := some (fcmpOp ft' a y) } : Eff)) = .ok e)
    (h1 : ft' = ft) : Out L p s e σ pc := by
  subst h1
  simp only [fpP] at h
  by_cases hc : (p.from_.type == AddrType.FCONST) = true
  · simp only [hc, ↓reduceIte, bind_assoc, pg_pure, pg_ok_bind] at h he
    obtain ⟨n, hn, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    rw [(vP_eval hn).1, pg_ok_bind] at he
    obtain rfl := pg_ok_inj he
    exact .inl ⟨⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩, rfl⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, bind_assoc, pg_pure, pg_ok_bind] at h he
    obtain ⟨m, hm, h⟩ := pg_bind_ok h
    obtain ⟨n, hn, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    rw [(vP_eval hm).1, pg_ok_bind, (vP_eval hn).1, pg_ok_bind] at he
    obtain rfl := pg_ok_inj he
    exact .inl ⟨⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩, rfl⟩

private theorem fp_csel {ft ft' : BitVec 2}
    (h : fpP (.csel ft) p = .ok (σ, pc))
    (he : (do
      let cond ← ProgOp.condOfSpecial p.from_
      let n ← ProgCtx.v ⟨L, s, p⟩ p.reg
      let q ← ProgCtx.rest ⟨L, s, p⟩ 0
      let m ← ProgCtx.v ⟨L, s, p⟩ q.reg
      ({} : Eff).wV p.to.reg (fpUn ft' (fun _ a => a) (if s.holds cond then n else m))) = .ok e)
    (h1 : ft' = ft) : Out L p s e σ pc := by
  subst h1
  simp only [fpP] at h
  obtain ⟨cc, hcc, h⟩ := pg_bind_ok h
  obtain ⟨n, hn, h⟩ := pg_bind_ok h
  obtain ⟨q, hq, h⟩ := pg_bind_ok h
  obtain ⟨m, hm, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  have hq' : ProgCtx.rest ⟨L, s, p⟩ 0 = .ok q := hq
  rw [hcc, pg_ok_bind, (vP_eval hn).1, pg_ok_bind, hq', pg_ok_bind, (vP_eval hm).1,
    pg_ok_bind] at he
  obtain ⟨hR, hpc⟩ := wVP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
  exact .inl ⟨hR, hpc⟩

private theorem fp_cvtz0 {u u' : Bool} {m m' : Nat}
    (h : fpP (.cvtz 0 u m) p = .ok (σ, pc))
    (he : (do
      let x ← ProgCtx.v ⟨L, s, p⟩ p.from_.reg
      ({} : Eff).wX p.to.reg
        ((GoFV.IEEE.toFixed .b32 (x.setWidth 32) u' m' .rz).setWidth 64)) = .ok e)
    (h1 : u' = u) (h2 : m' = m) : Out L p s e σ pc := by
  subst h1 h2
  simp only [fpP] at h
  obtain ⟨a, ha, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  rw [(vP_eval ha).1, pg_ok_bind] at he
  obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
  exact .inl ⟨hR, hpc⟩

private theorem fp_cvtz1 {u u' : Bool} {m m' : Nat}
    (h : fpP (.cvtz 1 u m) p = .ok (σ, pc))
    (he : (do
      let x ← ProgCtx.v ⟨L, s, p⟩ p.from_.reg
      ({} : Eff).wX p.to.reg
        ((GoFV.IEEE.toFixed .b64 (x.setWidth 64) u' m' .rz).setWidth 64)) = .ok e)
    (h1 : u' = u) (h2 : m' = m) : Out L p s e σ pc := by
  subst h1 h2
  simp only [fpP] at h
  obtain ⟨a, ha, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  rw [(vP_eval ha).1, pg_ok_bind] at he
  obtain ⟨hR, -, -, -, hpc⟩ := wP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
  exact .inl ⟨hR, hpc⟩

private theorem fp_cvtf0 {u u' : Bool} {m m' : Nat}
    (h : fpP (.cvtf 0 u m) p = .ok (σ, pc))
    (he : (do
      let x ← ProgCtx.x ⟨L, s, p⟩ p.from_.reg
      ({} : Eff).wV p.to.reg
        ((GoFV.IEEE.fromFixed .b32 m' (x.setWidth m') u' .rne).setWidth 128)) = .ok e)
    (h1 : u' = u) (h2 : m' = m) : Out L p s e σ pc := by
  subst h1 h2
  simp only [fpP] at h
  obtain ⟨a, ha, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  rw [(xP_eval ha).1, pg_ok_bind] at he
  obtain ⟨hR, hpc⟩ := wVP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
  exact .inl ⟨hR, hpc⟩

private theorem fp_cvtf1 {u u' : Bool} {m m' : Nat}
    (h : fpP (.cvtf 1 u m) p = .ok (σ, pc))
    (he : (do
      let x ← ProgCtx.x ⟨L, s, p⟩ p.from_.reg
      ({} : Eff).wV p.to.reg
        ((GoFV.IEEE.fromFixed .b64 m' (x.setWidth m') u' .rne).setWidth 128)) = .ok e)
    (h1 : u' = u) (h2 : m' = m) : Out L p s e σ pc := by
  subst h1 h2
  simp only [fpP] at h
  obtain ⟨a, ha, h⟩ := pg_bind_ok h
  obtain ⟨σ1, hσ1, h⟩ := pg_bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
  rw [(xP_eval ha).1, pg_ok_bind] at he
  obtain ⟨hR, hpc⟩ := wVP_rel (erel_init ⟨s, L.sym⟩) hσ1 he rfl
  exact .inl ⟨hR, hpc⟩

/-- The opcode names none of `progEffect`'s branches before the floating-point one takes. -/
private def preFP (name : String) : Prop :=
  pre9 name ∧ ProgOp.movMem name = none ∧ ProgOp.pairOp name = none ∧
  ProgOp.startsS name "LDAR" = false ∧ ProgOp.startsS name "LDAXR" = false ∧
  ProgOp.startsS name "STLR" = false ∧ ProgOp.startsS name "STLXR" = false ∧
  ProgOp.startsS name "CASAL" = false ∧ (ProgOp.rmw name).isNone = true

private theorem fp_pre {name : String} {k : FpOp} (h : fpOp? name = some k) : preFP name := by
  unfold fpOp? at h
  split at h <;> cases h <;> (unfold preFP pre9; decide)

set_option hygiene false in
/-- `progEffect` (`he`) reduced, for each name `fpOp?` (`hk`) maps to the family at hand, to its
floating-point branch with the name's fields as `progEffect` computes them. -/
local macro "fp_names_tac" : tactic => `(tactic| (
  obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩, q10, q11, q12, q13, q14, q15, q16, q17⟩ := fp_pre hk
  have q17' : ProgOp.rmw p.as.name = none := Option.isNone_iff_eq_none.mp q17
  unfold progEffect at he
  simp only [q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17',
    Bool.false_or, Bool.or_false, Bool.false_eq_true, ↓reduceIte] at he
  clear q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q17'
  generalize p.as.name = name at hk he
  unfold fpOp? at hk
  split at hk <;> cases hk <;>
    simp (config := { decide := true }) only [ProgOp.fpType, ↓reduceIte] at he))

private theorem fam_fpk1 {ft : BitVec 2} {opc : BitVec 6} (hk : fpOp? p.as.name = some (.fp1 ft opc))
    (h : fpP (.fp1 ft opc) p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  fp_names_tac
  all_goals exact fp_fp1 h he (by decide) (by decide)

private theorem fam_fpk2 {ft : BitVec 2} {opc : BitVec 4} (hk : fpOp? p.as.name = some (.fp2 ft opc))
    (h : fpP (.fp2 ft opc) p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  fp_names_tac
  all_goals exact fp_fp2 h he (by decide) (by decide)

private theorem fam_fpk3 {ft : BitVec 2} {o1 o0 : Bool} (hk : fpOp? p.as.name = some (.fp3 ft o1 o0))
    (h : fpP (.fp3 ft o1 o0) p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  fp_names_tac
  all_goals exact fp_fp3 h he (by decide) (by decide) (by decide)

private theorem fam_fcmp {ft : BitVec 2} (hk : fpOp? p.as.name = some (.cmp ft))
    (h : fpP (.cmp ft) p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  fp_names_tac
  all_goals exact fp_cmp h he (by decide)

private theorem fam_fcsel {ft : BitVec 2} (hk : fpOp? p.as.name = some (.csel ft))
    (h : fpP (.csel ft) p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  fp_names_tac
  all_goals exact fp_csel h he (by decide)

private theorem fam_fcvtz {ft : BitVec 2} {u : Bool} {m : Nat} (hk : fpOp? p.as.name = some (.cvtz ft u m))
    (h : fpP (.cvtz ft u m) p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  fp_names_tac
  all_goals first
    | (have h' : fpP (.cvtz 0 _ _) p = .ok (σ, pc) := h
       exact fp_cvtz0 h' he (by decide) (by decide))
    | exact fp_cvtz1 h he (by decide) (by decide)

private theorem fam_fcvtf {ft : BitVec 2} {u : Bool} {m : Nat} (hk : fpOp? p.as.name = some (.cvtf ft u m))
    (h : fpP (.cvtf ft u m) p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  fp_names_tac
  all_goals first
    | (have h' : fpP (.cvtf 0 _ _) p = .ok (σ, pc) := h
       exact fp_cvtf0 h' he (by decide) (by decide))
    | exact fp_cvtf1 h he (by decide) (by decide)

/-- The SIMD&FP data processing `fpOp?` names. -/
private theorem fam_fp {k : FpOp} (hk : fpOp? p.as.name = some k)
    (h : fpP k p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) : Out L p s e σ pc := by
  cases k with
  | fp1 => exact fam_fpk1 hk h he
  | fp2 => exact fam_fpk2 hk h he
  | fp3 => exact fam_fpk3 hk h he
  | cmp => exact fam_fcmp hk h he
  | csel => exact fam_fcsel hk h he
  | cvtz => exact fam_fcvtz hk h he
  | cvtf => exact fam_fcvtf hk h he

/-- `DMB` and `PRFM` have no effect (`progEffect`'s `DMB`/`PRFM` arm). -/
private theorem eff_barrier (hn : p.as.name = "DMB" ∨ p.as.name = "PRFM") :
    progEffect ⟨L, s, p⟩ = .ok {} := by
  unfold progEffect
  rcases hn with hn | hn <;>
    simp (config := { decide := true }) only [hn, ProgOp.baseOf, ↓reduceIte, ProgOp.movMem,
      ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS] <;> rfl

/-- The opcodes `progSym` matches by name. -/
private theorem fam_rest
    (hb1 : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] = none)
    (hb2 : ProgOp.baseOf p.as.name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] = none)
    (hb3 : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] = none)
    (hb4 : ProgOp.baseOf p.as.name ["NEG"] = none)
    (hb5 : ProgOp.baseOf p.as.name ["UBFX", "SBFX", "UBFIZ"] = none)
    (hm0 : ProgOp.movMem p.as.name = none) (hp0 : ProgOp.pairOp p.as.name = none)
    (hc0 : ProgOp.bcond p.as.name = none)
    (hmul : ProgOp.baseOf p.as.name ["MUL", "MNEG", "MADD", "MSUB", "UMULH", "SMULH"] = none)
    (hdp1 : ProgOp.baseOf p.as.name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none)
    (hcsel : ProgOp.baseOf p.as.name ["CSEL", "CSINC", "CSINV", "CSNEG", "CSET", "CSETM"] = none)
    (hex : exclOp p.as.name = none)
    (hdp2 : ProgOp.baseOf p.as.name
      ["ROR", "UDIV", "SDIV", "REM", "UREM", "BIC", "ORN", "EON", "MVN"] = none)
    (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e) :
    Out L p s e σ pc := by
  unfold progSymCore at h
  simp only [hb1, hb2, hb3, hb4, hb5, hm0, hp0, hc0, hmul, hdp1, hcsel, hex, hdp2] at h
  split at h
  · next _ hn =>
    by_cases h0 : (p.from_.offset == 0) = true
    case neg => simp only [h0, Bool.false_eq_true, ↓reduceIte] at h; cases h
    simp only [h0, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    unfold progEffect at he
    simp (config := { decide := true }) only [hn, ProgOp.baseOf, ProgOp.movMem, ProgOp.pairOp,
      ProgOp.rmw, ProgOp.bcond, ↓reduceIte] at he
    obtain rfl := pg_ok_inj he
    exact .inl ⟨erel_init _, rfl⟩
  · next _ hn =>
    by_cases h0 : (p.from_.type == .CONST && p.to.type == .NONE) = true
    case neg => simp only [h0, Bool.false_eq_true, ↓reduceIte] at h; cases h
    simp only [h0, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    obtain rfl := pg_ok_inj ((eff_barrier (.inl hn)).symm.trans he)
    exact .inl ⟨erel_init _, rfl⟩
  · next _ hn =>
    by_cases h0 : (p.from_.type == .MEM && p.from_.name == .NONE && p.from_.offset == 0 &&
      p.from_.index == 0 && p.to.type == .CONST) = true
    case neg => simp only [h0, Bool.false_eq_true, ↓reduceIte] at h; cases h
    simp only [h0, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    obtain rfl := pg_ok_inj ((eff_barrier (.inr hn)).symm.trans he)
    exact .inl ⟨erel_init _, rfl⟩
  · next _ hn =>
    by_cases hb : p.to.type = .BRANCH
    case neg => simp only [hb, beq_iff_eq, ↓reduceIte] at h; cases h
    simp only [hb, beq_self_eq_true, ↓reduceIte] at h
    obtain ⟨id, hid, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    unfold progEffect at he
    simp (config := { decide := true }) only [hn, ProgOp.baseOf, ProgOp.movMem, ProgOp.pairOp,
      ProgOp.rmw, ProgOp.bcond, ↓reduceIte, hb, beq_self_eq_true] at he
    obtain ⟨t, ht, he⟩ := pg_bind_ok he
    obtain rfl := pg_ok_inj he
    exact .inl ⟨⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩, t, targetP_eval hid ht, rfl⟩
  · next _ hn =>
    obtain ⟨a, hx, h⟩ := pg_bind_ok h
    obtain ⟨id, hid, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    exact fam_cbz (.inl hn) hx hid he
  · next _ hn =>
    obtain ⟨a, hx, h⟩ := pg_bind_ok h
    obtain ⟨id, hid, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    exact fam_cbz (.inr (.inl hn)) hx hid he
  · next _ hn =>
    obtain ⟨a, hx, h⟩ := pg_bind_ok h
    obtain ⟨id, hid, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    exact fam_cbz (.inr (.inr (.inl hn))) hx hid he
  · next _ hn =>
    obtain ⟨a, hx, h⟩ := pg_bind_ok h
    obtain ⟨id, hid, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    exact fam_cbz (.inr (.inr (.inr hn))) hx hid he
  · next _ hn =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    by_cases hb : (p.from_.offset < 0 ∨ p.from_.offset ≥ 64)
    · simp only [hb, ↓reduceIte] at h; cases h
    simp only [hb, ↓reduceIte] at h
    obtain ⟨a, hx, h⟩ := pg_bind_ok h
    obtain ⟨id, hid, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    exact fam_tbz (.inl hn) hx hid he
  · next _ hn =>
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    by_cases hb : (p.from_.offset < 0 ∨ p.from_.offset ≥ 64)
    · simp only [hb, ↓reduceIte] at h; cases h
    simp only [hb, ↓reduceIte] at h
    obtain ⟨a, hx, h⟩ := pg_bind_ok h
    obtain ⟨id, hid, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    exact fam_tbz (.inr hn) hx hid he
  · next _ hn =>
    unfold progEffect at he
    simp (config := { decide := true }) only [hn, ProgOp.baseOf, ProgOp.movMem, ProgOp.pairOp,
      ProgOp.rmw, ProgOp.bcond, ↓reduceIte] at he
    by_cases hm : (p.to.type == AddrType.MEM &&
        (p.to.name == AddrName.EXTERN || p.to.name == AddrName.STATIC)) = true
    · have hty : p.to.type = .MEM := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hm; exact hm.1
      simp only [hm, ↓reduceIte] at h
      have hnb : (p.to.type == AddrType.BRANCH) = false := by rw [hty]; rfl
      simp only [hnb, hm, Bool.false_eq_true, ↓reduceIte] at he
      cases hsym : p.to.sym with
      | none => simp only [hsym] at h; cases h
      | some n =>
        simp only [hsym] at h he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
        simp only [pg_pure, pg_ok_bind] at he
        obtain ⟨f, hf, he⟩ := pg_bind_ok he
        rw [wX_30, pg_ok_bind] at he
        obtain rfl := pg_ok_inj he
        exact .inr (.inl ⟨n, p.to.offset, f, rfl, rfl, fall_ok hf, rfl⟩)
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hb : (p.to.type == AddrType.BRANCH) = true
      case neg =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
        simp only [hb, hm, Bool.false_eq_true, ↓reduceIte] at he
        obtain ⟨a, hx, h⟩ := pg_bind_ok h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
        rw [(xP_eval hx).1, pg_ok_bind] at he
        obtain ⟨f, hf, he⟩ := pg_bind_ok he
        rw [wX_30, pg_ok_bind] at he
        obtain rfl := pg_ok_inj he
        refine .inr (.inr ⟨a, f, rfl, rfl, ?_, fall_ok hf, rfl⟩)
        have hbF : (p.to.type == AddrType.BRANCH) = false := by simpa using hb
        have hmF : (p.to.type == AddrType.MEM &&
            (p.to.name == AddrName.EXTERN || p.to.name == AddrName.STATIC)) = false := by
          simpa using hm
        show (p.as.name == "CALL" && !(p.to.type == AddrType.BRANCH) &&
          !(p.to.type == AddrType.MEM &&
            (p.to.name == AddrName.EXTERN || p.to.name == AddrName.STATIC))) = true
        rw [hn, hbF, hmF]
        rfl
      simp only [hb, ↓reduceIte] at h he
      split at h
      · cases h
      · next _ _ n hsym hv =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
        rw [target_sym (by simpa using hb) hv hsym, pg_ok_bind] at he
        obtain ⟨f, hf, he⟩ := pg_bind_ok he
        rw [wX_30, pg_ok_bind] at he
        obtain rfl := pg_ok_inj he
        exact .inr (.inl ⟨n, p.to.offset, f, rfl, rfl, fall_ok hf, rfl⟩)
      · cases h
  · next _ hn =>
    obtain ⟨a, hx, h⟩ := pg_bind_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pg_ok_inj h)
    unfold progEffect at he
    simp (config := { decide := true }) only [hn, ProgOp.baseOf, ProgOp.movMem, ProgOp.pairOp,
      ProgOp.rmw, ProgOp.bcond, ↓reduceIte] at he
    by_cases hN : (p.to.type == .NONE || p.to.sym.isSome) = true
    · simp only [hN, ↓reduceIte] at he; cases he
    simp only [hN, Bool.false_eq_true, ↓reduceIte] at he
    have hN' : (p.to.type == .NONE) = false := by
      simp only [Bool.or_eq_true, not_or] at hN; simpa using hN.1
    simp only [hN', Bool.false_eq_true, ↓reduceIte] at hx
    simp only [(xP_eval hx).1, pg_ok_bind] at he
    obtain rfl := pg_ok_inj he
    exact .inl ⟨⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩, rfl⟩
  · split at h
    · next k hk => exact fam_fp hk h he
    · cases h

private theorem dispatch {az ez : Int} {p : Prog} {σ : Sym} {pc : PCtl} {L : Link} {s : MState}
    {e : Eff} (h : progSymCore az ez p = .ok (σ, pc)) (he : progEffect ⟨L, s, p⟩ = .ok e)
    (haz : L.autosize = az) (hez : L.extrasize = ez) : Out L p s e σ pc := by
  cases hb1 : ProgOp.baseOf p.as.name ["LSL", "LSR", "ASR"] with
  | some r => obtain ⟨op, sf⟩ := r; exact fam_shift hb1 h he
  | none =>
  cases hb2 : ProgOp.baseOf p.as.name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] with
  | some r => obtain ⟨op, sf⟩ := r; exact fam_add hb1 hb2 h he
  | none =>
  cases hb3 : ProgOp.baseOf p.as.name ["CMP", "CMN", "TST"] with
  | some r => obtain ⟨op, sf⟩ := r; exact fam_cmp hb1 hb2 hb3 h he
  | none =>
  cases hb4 : ProgOp.baseOf p.as.name ["NEG"] with
  | some r => obtain ⟨op, sf⟩ := r; exact fam_neg hb1 hb2 hb3 hb4 h he
  | none =>
  cases hb5 : ProgOp.baseOf p.as.name ["UBFX", "SBFX", "UBFIZ"] with
  | some r => obtain ⟨op, sf⟩ := r; exact fam_ubfx hb1 hb2 hb3 hb4 hb5 h he
  | none =>
  cases hm : ProgOp.movMem p.as.name with
  | some r => obtain ⟨n, sg, fp⟩ := r; exact fam_mov hb1 hb2 hb3 hb4 hb5 hm h he haz hez
  | none =>
  cases hp : ProgOp.pairOp p.as.name with
  | some r => obtain ⟨ld, n, sg, fp⟩ := r; exact fam_pair hb1 hb2 hb3 hb4 hb5 hm hp h he haz hez
  | none =>
  cases hc : ProgOp.bcond p.as.name with
  | some k => exact fam_bcond hb1 hb2 hb3 hb4 hb5 hm hp hc h he
  | none =>
  have h0 := h
  unfold progSymCore at h
  simp only [hb1, hb2, hb3, hb4, hb5, hm, hp, hc] at h
  cases hmul : ProgOp.baseOf p.as.name ["MUL", "MNEG", "MADD", "MSUB", "UMULH", "SMULH"] with
  | some r =>
    obtain ⟨op, sf⟩ := r
    simp only [hmul] at h
    rcases mul_pre hmul with ⟨hop, hbin⟩ | ⟨hop, q1, q2, q3, q4, q5⟩
    · exact fam_mulb hop hbin h he
    · exact fam_madd hop q1 q2 q3 q4 q5 h he
  | none =>
  cases hdp1 : ProgOp.baseOf p.as.name ["CLZ", "RBIT", "REV", "REV16", "REV32"] with
  | some r =>
    obtain ⟨op, sf⟩ := r
    simp only [hmul, hdp1] at h
    exact fam_dp1 hdp1 h he
  | none =>
  cases hcsel : ProgOp.baseOf p.as.name ["CSEL", "CSINC", "CSINV", "CSNEG", "CSET", "CSETM"] with
  | some r =>
    obtain ⟨op, sf⟩ := r
    simp only [hmul, hdp1, hcsel] at h
    exact fam_csel hcsel h he
  | none =>
  cases hex : exclOp p.as.name with
  | some r =>
    obtain ⟨ld, n⟩ := r
    simp only [hmul, hdp1, hcsel, hex] at h
    exact fam_excl haz hez hex h he
  | none =>
  cases hdp2 : ProgOp.baseOf p.as.name
      ["ROR", "UDIV", "SDIV", "REM", "UREM", "BIC", "ORN", "EON", "MVN"] with
  | some r =>
    obtain ⟨op, sf⟩ := r
    simp only [hmul, hdp1, hcsel, hex, hdp2] at h
    exact fam_dp2 hdp2 h he
  | none =>
  exact fam_rest hb1 hb2 hb3 hb4 hb5 hm hp hc hmul hdp1 hcsel hex hdp2 h0 he

end fam

/-- What `progSym` adds to `progSymCore`: the control's opcode check. -/
theorem progSym_core {az ez : Int} {p : Prog} {σ : Sym} {pc : PCtl}
    (h : progSym az ez p = .ok (σ, pc)) : progSymCore az ez p = .ok (σ, pc) ∧ ctlOp p pc = .ok () := by
  unfold progSym at h
  split at h
  · rename_i σ' c' hc
    split at h
    · rename_i hok
      cases h
      exact ⟨hc, hok⟩
    · cases h
  · cases h

/-- Calls (direct and through a register) come from `CALL`, register jumps from `RET`. -/
theorem progSym_ctl {az ez : Int} {p : Prog} {σ : Sym} {pc : PCtl}
    (h : progSym az ez p = .ok (σ, pc)) :
    (∀ n add, pc = .call n add → p.as = .CALL) ∧ (∀ a, pc = .callReg a → p.as = .CALL) ∧
      (∀ a, pc = .reg a → p.as = .RET) := by
  have hc := (progSym_core h).2
  refine ⟨fun n add hp => ?_, fun a hp => ?_, fun a hp => ?_⟩ <;> subst hp <;>
    simp only [ctlOp] at hc <;> split at hc <;>
    first
    | (rename_i h'; simpa using h')
    | cases hc

theorem progSym_sound {az ez : Int} {p : Prog} {σ : Sym} {pc : PCtl} {L : Link} {s s' : MState}
    (h : progSym az ez p = .ok (σ, pc)) (haz : L.autosize = az) (hez : L.extrasize = ez)
    (hskip : p.isSkip = false) (hs : progStep L p s = .ok s') :
    NoNil ⟨s, L.sym⟩ σ ∧ HoldsCore ⟨s, L.sym⟩ σ s' ∧ PcP L p σ s pc s' := by
  unfold progStep at hs
  cases hn : L.nextAddr p.id with
  | none => rw [hn] at hs; cases hs
  | some next =>
  rw [hn] at hs
  simp only [hskip, Bool.false_eq_true, ↓reduceIte] at hs
  cases he : progEffect ⟨L, s, p⟩ with
  | error msg => rw [he] at hs; cases hs
  | ok e =>
  rw [he] at hs
  cases hnil : e.nilAccess? with
  | some a => simp only [hnil] at hs; cases hs
  | none =>
  simp only [hnil] at hs
  obtain rfl := pg_ok_inj hs
  rcases dispatch (progSym_core h).1 he haz hez with ⟨hR, hP⟩ | ⟨n, add, f, rfl, rfl, hf, rfl⟩ |
    ⟨a, f, rfl, rfl, hic, hf, rfl⟩
  · obtain ⟨hN, hH, h30, hpc⟩ := erel_apply (next := next) hR hnil
    refine ⟨hN, hH, ?_⟩
    cases pc with
    | fall =>
      simp only [PRel] at hP
      exact ⟨by rw [hpc, hP]; exact hn, h30⟩
    | jmp id =>
      obtain ⟨t, ht, hp⟩ := hP
      exact ⟨by rw [hpc, hp]; exact ht, h30⟩
    | cond cc id =>
      obtain ⟨t, ht, hp⟩ := hP
      refine ⟨⟨next, t, hn, ht, ?_⟩, h30⟩
      rw [hpc, hp]; split <;> rfl
    | cbz sf nz a id =>
      obtain ⟨t, ht, hp⟩ := hP
      refine ⟨⟨next, t, hn, ht, ?_⟩, h30⟩
      rw [hpc, hp]; split <;> rfl
    | tbz nz b a id =>
      obtain ⟨t, ht, hp⟩ := hP
      refine ⟨⟨next, t, hn, ht, ?_⟩, h30⟩
      rw [hpc, hp]; split <;> rfl
    | reg a =>
      simp only [PRel] at hP
      exact ⟨by rw [hpc, hP]; rfl, h30⟩
    | call n add => exact hP.elim
    | callReg a => exact hP.elim
  · have hR : ERel ⟨s, L.sym⟩ { x := [(30, f)], pc := some (L.sym n + BitVec.ofInt 64 add) }
        { x := [(30, .k f)] } :=
      ⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩
    obtain ⟨-, hH, h30, hpc⟩ := erel_apply (next := next) hR hnil
    refine ⟨⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩,
      ⟨fun r hr => ?_, hH.x31, hH.sp, hH.nzcv, hH.v, hH.mem⟩, ⟨by rw [hpc]; rfl, ?_⟩⟩
    · rw [hH.x r hr]
      have : (r == 30) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
      simp only [Sym.getX, List.lookup, this]
    · rw [h30]; exact hf
  · have hR : ERel ⟨s, L.sym⟩ { x := [(30, f)], pc := some (a.eval ⟨s, L.sym⟩) }
        { x := [(30, .k f)] } :=
      ⟨rfl, by simp, rfl, rfl, rfl, by simp, rfl, rfl⟩
    obtain ⟨-, hH, h30, hpc⟩ := erel_apply (next := next) hR hnil
    refine ⟨⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩,
      ⟨fun r hr => ?_, hH.x31, hH.sp, hH.nzcv, hH.v, hH.mem⟩, ⟨by rw [hpc]; rfl, ?_, hic⟩⟩
    · rw [hH.x r hr]
      have : (r == 30) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
      simp only [Sym.getX, List.lookup, this]
    · rw [h30]; exact hf

/-- A Prog `progSym` describes whose step faults in the nil page has a symbolic access there. -/
theorem progSym_fault {az ez : Int} {p : Prog} {σ : Sym} {pc : PCtl} {L : Link} {s : MState}
    {a : BitVec 64} (h : progSym az ez p = .ok (σ, pc)) (haz : L.autosize = az)
    (hez : L.extrasize = ez) (hs : progStep L p s = .error (.nilPage a)) :
    ¬ NoNil ⟨s, L.sym⟩ σ := by
  intro hN
  unfold progStep at hs
  cases hn : L.nextAddr p.id with
  | none => rw [hn] at hs; cases hs
  | some next =>
  rw [hn] at hs
  cases hsk : p.isSkip
  case true => simp only [hsk, ↓reduceIte] at hs; cases hs
  simp only [hsk, Bool.false_eq_true, ↓reduceIte] at hs
  cases he : progEffect ⟨L, s, p⟩ with
  | error msg => rw [he] at hs; cases hs
  | ok e =>
  rw [he] at hs
  cases hnil : e.nilAccess? with
  | none => simp only [hnil] at hs; cases hs
  | some a' =>
  have hnil' := hnil
  unfold Eff.nilAccess? at hnil'
  have hfound := List.find?_some hnil'
  have hmem := List.mem_of_find?_eq_some hnil'
  rcases dispatch (progSym_core h).1 he haz hez with ⟨hR, -⟩ | ⟨n, add, f, -, -, -, rfl⟩ |
    ⟨b, f, -, -, -, -, rfl⟩
  · rw [hR.loads, hR.stores] at hmem
    simp only [List.mem_append, List.map_map, List.mem_map, Function.comp_def] at hmem
    rcases hmem with ⟨⟨x, n⟩, hx, rfl⟩ | ⟨⟨x, n, v⟩, hx, rfl⟩
    · have := hN.1 x n hx
      simp only at hfound
      rw [this] at hfound
      cases hfound
    · have := hN.2 x n v hx
      simp only at hfound
      rw [this] at hfound
      cases hfound
  · simp at hmem
  · simp at hmem

end GoFV.Proof.Obj
