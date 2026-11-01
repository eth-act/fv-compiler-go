import GoFV.Proof.Pass.LoadFwdMem
import GoFV.Proof.Pass.RewriteTermDen

/-!
# Load-of-Store forwarding: pointers that evaluate alike (issue #151)

The validator's pointer relations, for a valuation `ρ` that is typed (`Term.Typed`) and whose
memory roots and `LocalAddr`s hold their definitions (`AtomSim.MemAtoms`), at every fuel:

* `ptrBase_den`: a pointer that evaluates to `P` is its base's pointer plus the offset
  (`RewriteCheck.ptrBase`: `OffPtr`s and `Copy`s at pointer shapes);
* `baseBlk_den`: a `LocalAddr`/`Addr` evaluates to the start of its allocation;
* `baseSame_den`, `samePtr_den`: pointers `baseSameB`/`samePtrB` relates are equal where both
  are pointers;
* `disjoint_sep`: pointers `disjointB` relates address separate bytes (`CSE.Mem.Sep`), so a
  `Load` reads through a `Store` at the other one (`load_write_sep`).
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.CSE.Mem GoFV.Proof.Pass.Rewrite

theorem toList_one {a : Array ID} (h : a.size = 1) : a.toList = [a[0]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, l⟩⟩⟩ <;> simp_all

theorem toList_two {a : Array ID} (h : a.size = 2) : a.toList = [a[0]!, a[1]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩⟩ <;> simp_all

theorem toList_three {a : Array ID} (h : a.size = 3) : a.toList = [a[0]!, a[1]!, a[2]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨z', l⟩⟩⟩⟩⟩ <;> simp_all

theorem not_term_of {D : ID → Option Value} {x : ID} {v : Value} (hv : D x = some v)
    (ht : ¬ termOp v.op = true) : ¬ IsTerm D x := fun ⟨w, hw, hw'⟩ => by
  rw [hv] at hw; cases hw; exact ht hw'

theorem evalPure_copy (ty : Ty) (ai : Int64) (aux : Option AuxRef) (y : Val) :
    evalPure .Copy ty ai aux [y] = y := rfl

theorem evalPure_load (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure .Load ty ai aux args = loadOp ty args := rfl

theorem evalPure_offPtr (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure .OffPtr ty ai aux args = PtrOps.offPtr ai args := rfl

theorem evalPure_addPtr (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure .AddPtr ty ai aux args = PtrOps.addPtr args := rfl

theorem evalPure_ptrIndex (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure .PtrIndex ty ai aux args =
      PtrOps.ptrIndex (match ty with | .ptr e => e | _ => none) args := rfl

/-- A value retyped at a pointer shape is a pointer when it stays one: retyping keeps a
pointer's allocation and offset. -/
theorem retype_ptr_eq {q P : Ptr} {t : Ty} (h : (Val.ptr q).retype t = .ptr P) : P = q := by
  cases t with
  | int w =>
    cases w with
    | w64 =>
      simp only [Val.retype] at h
      split at h
      · cases h
      · cases h; rfl
    | _ => simp [Val.retype] at h
  | ptr e => simp only [Val.retype] at h; cases h; rfl
  | _ => simp [Val.retype] at h

/-- Retyping at pointer shapes forgets the element size. -/
theorem retype_ptr_elem (e e' : Option Nat) (v : Val) :
    v.retype (.ptr e) = v.retype (.ptr e') := by
  cases v with
  | int w x => cases w <;> rfl
  | _ => rfl

/-- A value fixed by retyping at a pointer shape is `poison` or a pointer. -/
theorem ptr_fixed {t : Ty} (ht : isPtrTy t = true) {w : Val} (h : w.retype t = w) :
    w = .poison ∨ ∃ p, w = .ptr p := by
  cases t with
  | ptr e =>
    cases w with
    | poison => exact .inl rfl
    | ptr p => exact .inr ⟨p, rfl⟩
    | int w x => cases w <;> simp [Val.retype] at h
    | _ => simp [Val.retype] at h
  | _ => simp [isPtrTy] at ht

theorem ptr_refines {p : Ptr} {v : Val} (h : Sem.Refines (.ptr p) v) : v = .ptr p := by
  cases h; rfl

theorem ptr_add_zero (p : Ptr) : p.add 0 = p := by
  simp [Ptr.add]

theorem ptr_add_add (p : Ptr) (a b : BitVec 64) : (p.add a).add b = p.add (a + b) := by
  simp [Ptr.add, BitVec.add_assoc]

/-- Two fuels of one pointer-valued term agree. -/
theorem den_ptr_fuel {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {x : ID}
    {k k' : Nat} {p q : Ptr} (h : den D tabs ρ k x = .ptr p) (h' : den D tabs ρ k' x = .ptr q) :
    p = q := by
  rcases Nat.le_total k k' with hk | hk
  · have := den_fuel_mono D tabs ρ k k' x hk
    rw [h, h'] at this; cases this; rfl
  · have := den_fuel_mono D tabs ρ k' k x hk
    rw [h, h'] at this; cases this; rfl

section
variable {tabs : Tables} {f : Func} {ρ : ID → Val}

/-- The value of a defined node is fixed by retyping at its shape. -/
theorem den_fix (hT : Term.Typed f.value? tabs ρ) {x : ID} {v : Value} (hv : f.value? x = some v)
    (k : Nat) : (den f.value? tabs ρ k x).retype (tabs.ty v.type) = den f.value? tabs ρ k x := by
  cases k with
  | zero => simp [den, Val.retype]
  | succ k =>
    by_cases ht : IsTerm f.value? x
    · obtain ⟨w, hw, hwt⟩ := ht
      rw [hv] at hw; cases hw
      rw [den_succ_term hv hwt, Val.retype_idem]
    · rw [den_succ_atom ht]
      have := hT x ht (by rw [hv]; rfl)
      simpa [shape, hv] using this

/-- A pointer-shaped value is `poison` or a pointer. -/
theorem den_ptrVal (hT : Term.Typed f.value? tabs ρ) {x : ID} (hx : ptrVal tabs f x = true)
    (k : Nat) : den f.value? tabs ρ k x = .poison ∨ ∃ p, den f.value? tabs ρ k x = .ptr p := by
  unfold ptrVal at hx
  cases hv : f.value? x with
  | none => rw [hv] at hx; simp at hx
  | some v =>
    rw [hv] at hx
    exact ptr_fixed (by simpa using hx) (den_fix hT hv k)

theorem constIdx_spec {i : ID} {kk : BitVec 64} (h : constIdx? tabs f i = some kk) :
    ∃ iv, f.value? i = some iv ∧ iv.op = .Const64 ∧ tabs.ty iv.type = .int .w64 ∧
      kk = BitVec.ofInt 64 iv.auxInt.toInt := by
  unfold constIdx? at h
  split at h
  · next iv hiv =>
    split at h
    · next hop hty => cases h; exact ⟨iv, hiv, hop, hty, rfl⟩
    · cases h
  · cases h

/-- A `Const64` of the 64-bit integer shape evaluates to its constant. -/
theorem den_const64 {i : ID} {iv : Value} (hiv : f.value? i = some iv) (hop : iv.op = .Const64)
    (hty : tabs.ty iv.type = .int .w64) (k : Nat) :
    den f.value? tabs ρ (k + 1) i = .int .w64 (BitVec.ofInt 64 iv.auxInt.toInt) := by
  have ht : termOp iv.op = true := by rw [hop]; rfl
  have hfo : GoFV.Proof.Rules.frameOp iv.op = false := by rw [hop]; rfl
  rw [den_succ_term hiv ht, GoFV.Proof.Rules.opVal_pure hfo, hop, hty]
  rw [show ∀ (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val),
    evalPure .Const64 ty ai aux args = Conv.const .w64 ai from fun _ _ _ _ => rfl]
  simp only [Conv.const, Val.retype]
  simp

/-- A `PtrIndex` by a constant index: the pointer plus the index times the element size. -/
theorem ptrIndex_den (hT : Term.Typed f.value? tabs ρ) {a : ID} {u : Value}
    (hu : f.value? a = some u) (hop : u.op = .PtrIndex) (hsz : u.args.size = 2)
    (hpv : ptrVal tabs f u.args[0]! = true) {e : Nat} (hty : tabs.ty u.type = .ptr (some e))
    {kk : BitVec 64} (hci : constIdx? tabs f u.args[1]! = some kk) {k : Nat} {p : Ptr}
    (h : den f.value? tabs ρ k a = .ptr p) :
    ∃ q, den f.value? tabs ρ (k - 1) u.args[0]! = .ptr q ∧ p = q.add (kk * BitVec.ofNat 64 e) := by
  obtain ⟨iv, hiv, hiop, hity, rfl⟩ := constIdx_spec hci
  have ht : termOp u.op = true := by rw [hop]; rfl
  have hfo : GoFV.Proof.Rules.frameOp u.op = false := by rw [hop]; rfl
  cases k with
  | zero => simp [den] at h
  | succ k =>
  simp only [Nat.add_sub_cancel]
  rw [den_succ_term hu ht, toList_two hsz, List.map_cons, List.map_cons, List.map_nil,
    GoFV.Proof.Rules.opVal_pure hfo, hop, evalPure_ptrIndex, hty] at h
  cases k with
  | zero => simp [den, PtrOps.ptrIndex, Val.retype] at h
  | succ k =>
  rw [den_const64 hiv hiop hity k] at h
  rcases den_ptrVal hT hpv (k + 1) with h0 | ⟨q0, h0⟩
  · rw [h0] at h; simp [PtrOps.ptrIndex, Val.retype] at h
  · refine ⟨q0, h0, ?_⟩
    rw [h0] at h
    simp only [PtrOps.ptrIndex, asOffset, PtrOps.ptrRes] at h
    split at h
    · rw [retype_ptr_eq h]; simp
    · simp [Val.retype] at h

/-- One `ptrStep?`: the argument's pointer plus the offset. -/
theorem ptrStep_den (hT : Term.Typed f.value? tabs ρ) {a c : ID} {o : BitVec 64}
    (hs : ptrStep? tabs f a = some (c, o)) {k : Nat} {p : Ptr}
    (h : den f.value? tabs ρ k a = .ptr p) : ∃ q, den f.value? tabs ρ (k - 1) c = .ptr q ∧ p = q.add o := by
  unfold ptrStep? at hs
  cases hu : f.value? a with
  | none => rw [hu] at hs; cases hs
  | some u =>
  rw [hu] at hs
  dsimp only at hs
  split at hs
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨hop, hsz⟩, -⟩, hpv⟩ := hc
    have ht : termOp u.op = true := by rcases hop with h | h <;> rw [h] <;> rfl
    have hfo : GoFV.Proof.Rules.frameOp u.op = false := by
      rcases hop with h | h <;> rw [h] <;> rfl
    cases k with
    | zero => simp [den] at h
    | succ k =>
    simp only [Nat.add_sub_cancel]
    rw [den_succ_term hu ht, toList_one hsz, List.map_cons, List.map_nil,
      GoFV.Proof.Rules.opVal_pure hfo] at h
    rcases den_ptrVal hT hpv k with h0 | ⟨q0, h0⟩
    · rw [h0] at h
      rcases hop with hop | hop <;> rw [hop] at h
      · rw [evalPure_offPtr] at h; simp [PtrOps.offPtr, Val.retype] at h
      · rw [evalPure_copy] at h; simp [Val.retype] at h
    · refine ⟨q0, h0, ?_⟩
      rw [h0] at h
      rcases hop with hop | hop
      · rw [hop, evalPure_offPtr] at h
        simp only [PtrOps.offPtr, PtrOps.ptrRes] at h
        split at h
        · rw [retype_ptr_eq h, hop]; rfl
        · simp [Val.retype] at h
      · rw [hop, evalPure_copy] at h
        rw [retype_ptr_eq h, hop]
        simp [Ptr.add]
  · split at hs
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hop, hsz⟩, hpv⟩ := hc
      split at hs
      · next e kk hty hci =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ptrIndex_den hT hu hop hsz hpv hty hci h
      · cases hs
    · cases hs

/-- **Base and offset**: a pointer is its `ptrBase`'s pointer plus the offset. -/
theorem ptrBase_den (hT : Term.Typed f.value? tabs ρ) :
    ∀ (n : Nat) (a : ID) (k : Nat) (p : Ptr), den f.value? tabs ρ k a = .ptr p →
      ∃ k' q, den f.value? tabs ρ k' (ptrBase tabs f n a).1 = .ptr q ∧
        p = q.add (ptrBase tabs f n a).2
  | 0, a, k, p, h => ⟨k, p, h, (ptr_add_zero p).symm⟩
  | n + 1, a, k, p, h => by
    cases hs : ptrStep? tabs f a with
    | none =>
      simp only [ptrBase, hs]
      exact ⟨k, p, h, (ptr_add_zero p).symm⟩
    | some co =>
      obtain ⟨c, o⟩ := co
      simp only [ptrBase, hs]
      obtain ⟨q0, h0, rfl⟩ := ptrStep_den hT hs h
      obtain ⟨k', q, hq, rfl⟩ := ptrBase_den hT n c (k - 1) q0 h0
      exact ⟨k', q, hq, ptr_add_add q _ o⟩

/-- A `LocalAddr`/`Addr` with a known allocation (`baseBlk?`) evaluates to its start. -/
theorem baseBlk_den (hM : MemAtoms f.value? tabs ρ) {a : ID} {B : Blk}
    (hB : baseBlk? tabs f a = some B) {k : Nat} {P : Ptr} (h : den f.value? tabs ρ k a = .ptr P) :
    P = ⟨B, 0⟩ := by
  unfold baseBlk? at hB
  cases hu : f.value? a with
  | none => rw [hu] at hB; cases hB
  | some u =>
    rw [hu] at hB
    dsimp only at hB
    cases k with
    | zero => simp [den] at h
    | succ k =>
    split at hB
    · rename_i hl
      rw [beq_iff_eq] at hl
      have hat : ¬ IsTerm f.value? a := not_term_of hu (by rw [hl]; decide)
      rw [den_succ_atom hat] at h
      obtain ⟨N, hN⟩ := hM a u hu (by rw [hl]; rfl) (by rw [h]; nofun)
      obtain ⟨y, hy, hρ⟩ := hN N (Nat.le_refl _)
      unfold memDef at hy
      rw [hl] at hy
      simp only [Option.some.injEq] at hy
      subst hy
      cases hax : u.aux with
      | none => rw [hax] at hB; cases hB
      | some n =>
        rw [hax] at hB; cases hB
        rw [h, hax] at hρ
        exact retype_ptr_eq hρ.symm
    · split at hB
      · rename_i _ hd
        rw [beq_iff_eq] at hd
        have ht : termOp u.op = true := by rw [hd]; rfl
        rw [den_succ_term hu ht, hd, GoFV.Proof.Rules.opVal_addr] at h
        unfold GoFV.Proof.Rules.addrVal at h
        split at hB
        · rename_i name _ _ _ hax
          cases hB
          rw [hax] at h
          exact retype_ptr_eq h
        · cases hB
      · cases hB

/-- `termEqB`: the two terms evaluate equally, at every fuel. -/
theorem termEq_den : ∀ (n : Nat) (a b : ID), termEqB tabs f n a b = true →
    ∀ k, den f.value? tabs ρ k a = den f.value? tabs ρ k b
  | 0, a, b, h, k => by simp only [termEqB, beq_iff_eq] at h; rw [h]
  | n + 1, a, b, h, k => by
    unfold termEqB at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · rfl
    split at h
    · rename_i u w hu hw
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨ht, hop⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := h
      cases k with
      | zero => rfl
      | succ k =>
        rw [den_succ_term hu ht, den_succ_term hw (hop ▸ ht), ← hop, ← tyEq_sound hty, hai, hax]
        congr 2
        apply List.ext_getElem (by simp [hsz])
        intro i h1 h2
        simp only [List.getElem_map, Array.getElem_toList]
        have h1' : i < u.args.size := by simpa using h1
        have h2' : i < w.args.size := by simpa using h2
        refine termEq_den n _ _ (hargs (u.args[i], w.args[i]) ?_) k
        have hz : i < (u.args.toList.zip w.args.toList).length := by
          simp only [List.length_zip, Array.length_toList]; omega
        have := List.getElem_mem hz
        simpa [List.getElem_zip] using this
    · cases h

/-- Offsets of `idxSame` indices agree where both are integers. -/
theorem idxSame_den {i j : ID} (h : idxSame tabs f i j = true) {k k' : Nat} {o o' : BitVec 64}
    (hi : asOffset (den f.value? tabs ρ k i) = some o)
    (hj : asOffset (den f.value? tabs ρ k' j) = some o') : o = o' := by
  have hint : ∀ {v w : Val}, Sem.Refines v w → ∀ {o}, asOffset v = some o → asOffset w = some o :=
    fun hr _ ho => by cases hr <;> first | rfl | (simp [asOffset] at ho; done) | exact ho
  rw [← termEq_den 4 i j h k'] at hj
  rcases Nat.le_total k k' with hk | hk
  · have := hint (den_fuel_mono _ _ _ _ _ _ hk) hi
    rw [hj] at this; cases this; rfl
  · have := hint (den_fuel_mono _ _ _ _ _ _ hk) hj
    rw [hi] at this; cases this; rfl

/-- `AddPtr`/`PtrIndex` on a pointer and an integer: the value depends on the index's offset. -/
theorem evalPure_ptrArith {op : Op} (hop : op = .AddPtr ∨ op = .PtrIndex) {t : Ty} {ai : Int64}
    {ax : Option AuxRef} {x i : Val} {P : Ptr} (ht : x = .poison ∨ ∃ p, x = .ptr p)
    (h : (evalPure op t ai ax [x, i]).retype t = .ptr P) :
    ∃ p o, x = .ptr p ∧ asOffset i = some o ∧
      ∀ i', asOffset i' = some o → evalPure op t ai ax [x, i'] = evalPure op t ai ax [x, i] := by
  rcases ht with rfl | ⟨p, rfl⟩
  · rcases hop with rfl | rfl
    · rw [evalPure_addPtr] at h; simp [PtrOps.addPtr, Val.retype] at h
    · rw [evalPure_ptrIndex] at h; simp [PtrOps.ptrIndex, Val.retype] at h
  · cases ho : asOffset i with
    | none =>
      rcases hop with rfl | rfl
      · rw [evalPure_addPtr] at h; simp [PtrOps.addPtr, ho, Val.retype] at h
      · rw [evalPure_ptrIndex] at h
        simp only [PtrOps.ptrIndex, ho] at h
        revert h; split <;> simp_all [Val.retype]
    | some o =>
      refine ⟨p, o, rfl, rfl, fun i' hi' => ?_⟩
      rcases hop with rfl | rfl
      · rw [evalPure_addPtr, evalPure_addPtr]; simp only [PtrOps.addPtr, ho, hi']
      · rw [evalPure_ptrIndex, evalPure_ptrIndex]; simp only [PtrOps.ptrIndex, ho, hi']

/-- **Equal bases** where both are pointers. -/
theorem baseSame_den (hT : Term.Typed f.value? tabs ρ) (hM : MemAtoms f.value? tabs ρ) :
    ∀ (n : Nat) (a b : ID), baseSameB tabs f n a b = true → ∀ {k k' : Nat} {p q : Ptr},
      den f.value? tabs ρ k a = .ptr p → den f.value? tabs ρ k' b = .ptr q → p = q
  | 0, a, b, h, k, k', p, q, ha, hb => by
    simp only [baseSameB, beq_iff_eq] at h
    subst h; exact den_ptr_fuel ha hb
  | n + 1, a, b, h, k, k', p, q, ha, hb => by
    unfold baseSameB at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ⟨h | h⟩ | h
    · subst h; exact den_ptr_fuel ha hb
    · split at h
      · rename_i x y hx hy
        rw [beq_iff_eq] at h; subst h
        rw [baseBlk_den hM hx ha, baseBlk_den hM hy hb]
      · cases h
    · cases hu : f.value? a with
      | none => rw [hu] at h; cases h
      | some u =>
      cases hw : f.value? b with
      | none => rw [hu, hw] at h; cases h
      | some w =>
      rw [hu, hw] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hop, hop'⟩, hsu⟩, hsw⟩, hty⟩, hai⟩, hax⟩, hpu⟩, hpw⟩, hoff⟩, hbase⟩,
        hidx⟩ := h
      have ht : termOp u.op = true := by rcases hop with h | h <;> rw [h] <;> rfl
      have hfo : GoFV.Proof.Rules.frameOp u.op = false := by
        rcases hop with h | h <;> rw [h] <;> rfl
      have hop2 : w.op = .AddPtr ∨ w.op = .PtrIndex := hop' ▸ hop
      have hargs : ∀ {v : Value}, v.args.size = 2 → v.args.toList = [v.args[0]!, v.args[1]!] :=
        fun hs => toList_two hs
      cases k with
      | zero => simp [den] at ha
      | succ k =>
      cases k' with
      | zero => simp [den] at hb
      | succ k' =>
      rw [den_succ_term hu ht, hargs hsu, List.map_cons, List.map_cons, List.map_nil,
        GoFV.Proof.Rules.opVal_pure hfo] at ha
      rw [den_succ_term hw (hop' ▸ ht), hargs hsw, List.map_cons, List.map_cons, List.map_nil,
        GoFV.Proof.Rules.opVal_pure (hop' ▸ hfo)] at hb
      obtain ⟨pa, oa, hpa, hoa, hia⟩ := evalPure_ptrArith hop (den_ptrVal hT hpu k) ha
      obtain ⟨pb, ob, hpb, hob, hib⟩ := evalPure_ptrArith hop2 (den_ptrVal hT hpw k') hb
      have hab : pa = pb := by
        obtain ⟨k1, qa, h1, e1⟩ := ptrBase_den hT 8 _ k pa hpa
        obtain ⟨k2, qb, h2, e2⟩ := ptrBase_den hT 8 _ k' pb hpb
        rw [e1, e2, hoff, baseSame_den hT hM n _ _ hbase h1 h2]
      have hoo : oa = ob := idxSame_den hidx hoa hob
      rw [hpa] at ha hia; rw [hpb, ← hab] at hb hib
      rw [← hib _ (hoo ▸ hoa), ← hop', ← tyEq_sound hty, ← hai, ← hax] at hb
      rw [ha] at hb; cases hb; rfl

/-- **Equal pointers** (`samePtrB`) where both are pointers. -/
theorem samePtr_den (hT : Term.Typed f.value? tabs ρ) (hM : MemAtoms f.value? tabs ρ) {a b : ID}
    (h : samePtrB tabs f a b = true) {k k' : Nat} {p q : Ptr}
    (ha : den f.value? tabs ρ k a = .ptr p) (hb : den f.value? tabs ρ k' b = .ptr q) : p = q := by
  unfold samePtrB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨k1, qa, h1, e1⟩ := ptrBase_den hT 8 a k p ha
  obtain ⟨k2, qb, h2, e2⟩ := ptrBase_den hT 8 b k' q hb
  rw [e1, e2, h.1, baseSame_den hT hM 8 _ _ h.2 h1 h2]

/-- Offsets `offSep` separates, from one base. -/
theorem offSep_sep {B : Ptr} {o o' : BitVec 64} {n k : Nat} (h : offSep o n o' k = true) :
    Sep (B.add o) n (B.add o') k := by
  unfold offSep at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  right; right; right
  simp only [Ptr.add, BitVec.toNat_add, BitVec.toNat_sub] at h ⊢
  have hB := B.off.isLt
  have ho := o.isLt
  have ho' := o'.isLt
  omega

/-- **Disjoint pointers** (`disjointB`) address separate bytes where both are pointers. -/
theorem disjoint_sep (hT : Term.Typed f.value? tabs ρ) (hM : MemAtoms f.value? tabs ρ) {a b : ID}
    {n m : Nat} (h : disjointB tabs f a n b m = true) {k k' : Nat} {p q : Ptr}
    (ha : den f.value? tabs ρ k a = .ptr p) (hb : den f.value? tabs ρ k' b = .ptr q) :
    Sep p n q m := by
  unfold disjointB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  obtain ⟨k1, qa, h1, e1⟩ := ptrBase_den hT 8 a k p ha
  obtain ⟨k2, qb, h2, e2⟩ := ptrBase_den hT 8 b k' q hb
  rcases h with ⟨hs, hb'⟩ | h
  · rw [e1, e2, ← baseSame_den hT hM 8 _ _ hb' h1 h2]
    exact offSep_sep hs
  · split at h
    · rename_i x y hx hy
      rw [bne_iff_ne] at h
      right; right; left
      rw [e1, e2, baseBlk_den hM hx h1, baseBlk_den hM hy h2]
      exact h
    · cases h

end

/-- A `Load` after a write separate from it reads what it read before. -/
theorem load_write_sep {m m' : Mem} {q p : Ptr} {bs : Array Byte} {t : Ty}
    (hw : m.write q bs = some m') (hs : Sep p t.size q bs.size) : m'.load t p = m.load t p := by
  unfold Mem.load
  split <;> first | rfl | rw [read_write_sep hw hs]

end GoFV.Proof.Pass.LoadFwd
