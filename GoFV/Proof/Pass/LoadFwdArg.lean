import GoFV.Proof.Pass.DAEPure
import GoFV.Proof.Pass.LoadFwdPtr
import GoFV.Proof.AtomSimEnter

variable [GoFV.SSA.Sem.Addrs]

/-!
# Argument pointers avoid the frame temporaries (issue #69)

A run's arguments hold no pointer into a frame temporary (`Sem.InitAvoids`), so neither do the
arguments' images, the `Arg`/`ArgIntReg` pieces decoded from them, nor the pointers
`RewriteCheck.argPtrB` steps from them (`OffPtr`, `Copy`, `AddPtr`, `PtrIndex`, `NilCheck`, which
keep the block of their first argument). `ArgAv`: the registers of such pointers avoid activation
0's frame temporaries (`Temp0`); a value's evaluation keeps it (`argAv_set`), and the terms over
registers with it avoid them too (`argPtr_den`). A frame temporary's `LocalAddr` therefore points
into another block than an argument's pointer (`RewriteCheck.disjointB`).
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.DAE GoFV.Proof.CSE.Mem

/-- Activation 0's frame temporaries (where the atom simulation runs). -/
def Temp0 (b : Blk) : Prop := ∃ n, b = .temp 0 n

theorem tempU_temp0 : TempU Temp0 := fun _ ⟨n, h⟩ => ⟨0, n, h⟩

/-! ## From `InitAvoids` -/

theorem byte_avoids_temp0 {x : Byte} (h : ∀ n, Byte.Avoids (· = .temp 0 n) x) :
    Byte.Avoids Temp0 x := by
  cases x with
  | frag p k => rintro ⟨n, hn⟩; exact h n hn
  | _ => trivial

mutual
theorem val_avoids_temp0 : {v : Val} → (∀ n, v.Avoids (· = .temp 0 n)) → Val.Avoids Temp0 v
  | .ptr _, h => by rintro ⟨n, hn⟩; exact h n hn
  | .tuple vs, h => valList_avoids_temp0 (vs := vs) h
  | .agg vs, h => valList_avoids_temp0 (vs := vs) h
  | .blob _, h => fun x hx => byte_avoids_temp0 fun n => h n x hx
  | .mem m, h => by
    intro b a hm hb x hx
    cases x with
    | frag p k =>
      rintro ⟨n, hn⟩
      exact h n b a hm (fun hb' => hb ⟨n, hb'⟩) _ hx hn
    | _ => trivial
  | .int _ _, _ | .bool _, _ | .empty, _ | .poison, _ => trivial
theorem valList_avoids_temp0 : {vs : List Val} → (∀ n, Val.AvoidsList (· = .temp 0 n) vs) →
    Val.AvoidsList Temp0 vs
  | [], _ => trivial
  | _ :: _, h => ⟨val_avoids_temp0 fun n => (h n).1, valList_avoids_temp0 fun n => (h n).2⟩
end

/-- The images of the entry frame's arguments avoid activation 0's frame temporaries. -/
theorem images_avoid {env : Env} {args : List Val} {mem : Mem} (h : InitAvoids env args mem)
    (ctx : Ctx) : ∀ img ∈ (entryFrame env ctx args mem).images, BAv Temp0 img := by
  intro img hi
  simp only [entryFrame, Array.mem_map] at hi
  obtain ⟨⟨a, t⟩, hm, rfl⟩ := hi
  have ha : a ∈ args := by
    have := (Array.of_mem_zip hm).1
    simpa using this
  exact encode_avoids t (val_avoids_temp0 fun n => (h 0 n).1 a ha)

/-! ## Pointer steps keep the block of their first argument -/

/-- `OffPtr`, `Copy`, `AddPtr` and `PtrIndex` of a first argument avoiding `U` avoid `U`. -/
theorem ptrStep_avoids {U : Blk → Prop} {op : Op}
    (hop : op = .OffPtr ∨ op = .Copy ∨ op = .AddPtr ∨ op = .PtrIndex) (ty : Ty) (ai : Int64)
    (ax : Option AuxRef) (args : List Val) (hx : ∀ z ∈ args.head?, Val.Avoids U z) :
    Val.Avoids U (evalPure op ty ai ax args) := by
  rcases hop with rfl | rfl | rfl | rfl
  · show Val.Avoids U (PtrOps.offPtr ai args)
    unfold PtrOps.offPtr
    split
    · exact ptrRes_avoids (hx _ rfl)
    · exact wordRes_avoids _ _
    · trivial
  · rcases args with _ | ⟨x, _ | ⟨y, l⟩⟩
    · trivial
    · exact hx x rfl
    · trivial
  · show Val.Avoids U (PtrOps.addPtr args)
    unfold PtrOps.addPtr
    split
    · split
      · exact ptrRes_avoids (hx _ rfl)
      · trivial
    · split
      · exact wordRes_avoids _ _
      · trivial
    · trivial
  · show Val.Avoids U (PtrOps.ptrIndex _ args)
    unfold PtrOps.ptrIndex
    split
    · split
      · exact ptrRes_avoids (hx _ rfl)
      · trivial
    · split
      · exact wordRes_avoids _ _
      · trivial
    · trivial

/-! ## Argument pointers -/

/-- The registers of argument pointers (`argPtrB`) avoid activation 0's frame temporaries. -/
def ArgAv (tabs : Tables) (f : Func) (ρ : ID → Val) : Prop :=
  ∀ n a, argPtrB tabs f n a = true → Val.Avoids Temp0 (ρ a)

theorem argAv_poison (tabs : Tables) (f : Func) : ArgAv tabs f fun _ => .poison :=
  fun _ _ _ => trivial

theorem argAv_pois {tabs : Tables} {f : Func} {ρ ρ' : ID → Val} (h : ArgAv tabs f ρ)
    (hρ : ∀ a, ρ' a = ρ a ∨ ρ' a = .poison) : ArgAv tabs f ρ' := fun n a ha => by
  rcases hρ a with e | e <;> rw [e]
  · exact h n a ha
  · trivial

/-- The cases of `argPtrB`. -/
theorem argPtrB_cases {tabs : Tables} {f : Func} {n : Nat} {a : ID}
    (h : argPtrB tabs f n a = true) :
    ∃ n' u, n = n' + 1 ∧ f.value? a = some u ∧
      (u.op = .Arg ∨ u.op = .ArgIntReg ∨
        (((u.op = .OffPtr ∨ u.op = .Copy) ∧ u.args.size = 1 ∨
          (u.op = .AddPtr ∨ u.op = .PtrIndex ∨ u.op = .NilCheck) ∧ u.args.size = 2) ∧
          argPtrB tabs f n' u.args[0]! = true)) := by
  cases n with
  | zero => simp [argPtrB] at h
  | succ n' =>
    unfold argPtrB at h
    cases hu : f.value? a with
    | none => rw [hu] at h; cases h
    | some u =>
      rw [hu] at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
      exact ⟨n', u, rfl, rfl, h⟩

theorem argPtrB_not_phi {tabs : Tables} {f : Func} {n : Nat} {a : ID}
    (h : argPtrB tabs f n a = true) : ∃ u, f.value? a = some u ∧ u.op ≠ .Phi := by
  obtain ⟨n', u, _, hu, hc⟩ := argPtrB_cases h
  refine ⟨u, hu, fun hp => ?_⟩
  rw [hp] at hc
  rcases hc with h | h | ⟨(⟨h | h, -⟩ | ⟨h | h | h, -⟩), -⟩ <;> cases h

private theorem args1 {xs : Array ID} (h : xs.size = 1) : xs.toList = [xs[0]!] := by
  rcases xs with ⟨_ | ⟨a, _ | ⟨b, l⟩⟩⟩ <;> simp_all

private theorem args2 {xs : Array ID} (h : xs.size = 2) : xs.toList = [xs[0]!, xs[1]!] := by
  rcases xs with ⟨_ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩⟩ <;> simp_all

/-- A term node of `argPtrB`'s steps on a first argument avoiding `Temp0`, at any arguments'
values. -/
theorem argStep_avoids₀ {tabs : Tables} {u : Value}
    (hop : (u.op = .OffPtr ∨ u.op = .Copy) ∧ u.args.size = 1 ∨
      (u.op = .AddPtr ∨ u.op = .PtrIndex) ∧ u.args.size = 2) (ty : Ty) (σ : ID → Val)
    (h0 : Val.Avoids Temp0 (σ u.args[0]!)) :
    Val.Avoids Temp0 (GoFV.Proof.Rules.opVal tabs u.op ty u.auxInt u.aux
      (u.args.toList.map σ)) := by
  have hfo : GoFV.Proof.Rules.frameOp u.op = false := by
    rcases hop with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> rw [h] <;> rfl
  rw [GoFV.Proof.Rules.opVal_pure hfo]
  rcases hop with ⟨hop, hs⟩ | ⟨hop, hs⟩
  · rw [args1 hs, List.map_cons]
    exact ptrStep_avoids (hop.elim .inl fun h => .inr (.inl h)) _ _ _ _
      fun z hz => by cases hz; exact h0
  · rw [args2 hs, List.map_cons]
    exact ptrStep_avoids (hop.elim (fun h => .inr (.inr (.inl h))) fun h => .inr (.inr (.inr h)))
      _ _ _ _ fun z hz => by cases hz; exact h0

theorem argStep_avoids {tabs : Tables} {u : Value}
    (hop : (u.op = .OffPtr ∨ u.op = .Copy) ∧ u.args.size = 1 ∨
      (u.op = .AddPtr ∨ u.op = .PtrIndex) ∧ u.args.size = 2) (σ : ID → Val)
    (h0 : Val.Avoids Temp0 (σ u.args[0]!)) :
    Val.Avoids Temp0 ((GoFV.Proof.Rules.opVal tabs u.op (tabs.ty u.type) u.auxInt u.aux
      (u.args.toList.map σ)).retype (tabs.ty u.type)) :=
  retype_avoids tempU_temp0 _ (argStep_avoids₀ hop _ σ h0)

/-- **Argument pointers as terms** avoid activation 0's frame temporaries, for valuations whose
argument pointers do (`ArgAv`). -/
theorem argPtr_den {tabs : Tables} {f : Func} {ρ : ID → Val} (hA : ArgAv tabs f ρ) :
    ∀ (n : Nat) (a : ID), argPtrB tabs f n a = true → ∀ k,
      Val.Avoids Temp0 (den f.value? tabs ρ k a)
  | n, a, h, 0 => by simp only [den]; trivial
  | n, a, h, k + 1 => by
    obtain ⟨n', u, rfl, hu, hc⟩ := argPtrB_cases h
    rcases hc with hop | hop | ⟨hop, h0⟩
    · rw [den_succ_atom (not_term_of hu (by rw [hop]; decide))]; exact hA _ a h
    · rw [den_succ_atom (not_term_of hu (by rw [hop]; decide))]; exact hA _ a h
    rcases hop with hop | ⟨hop | hop | hop, hs⟩
    · have ht : termOp u.op = true := by rcases hop with ⟨h | h, -⟩ <;> rw [h] <;> rfl
      rw [den_succ_term hu ht]
      exact argStep_avoids (.inl hop) _ (argPtr_den hA n' _ h0 k)
    · have ht : termOp u.op = true := by rw [hop]; rfl
      rw [den_succ_term hu ht]
      exact argStep_avoids (.inr ⟨.inl hop, hs⟩) _ (argPtr_den hA n' _ h0 k)
    · have ht : termOp u.op = true := by rw [hop]; rfl
      rw [den_succ_term hu ht]
      exact argStep_avoids (.inr ⟨.inr hop, hs⟩) _ (argPtr_den hA n' _ h0 k)
    · rw [den_succ_atom (not_term_of hu (by rw [hop]; decide))]; exact hA _ a h

/-! ## Evaluation keeps `ArgAv` -/

theorem argVal_avoids₀ {ctx : Ctx} {fr : Frame} (hi : ∀ img ∈ fr.images, BAv Temp0 img)
    {n : AuxRef} {off : Int} {ty : Ty} {r : Val} (h : argVal ctx fr n off ty = .ok r) :
    Val.Avoids Temp0 r := by
  unfold argVal at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i img himg
      split at h
      · cases h; trivial
      · cases h
        exact decode_avoids tempU_temp0 (hi img (Array.mem_of_getElem? himg)) _ _

/-- A `NilCheck` that does not panic gives its pointer. -/
theorem memRoot_nilCheck {ctx : Ctx} {v : Value} {a b r : Val} (hop : v.op = .NilCheck)
    (h : memRoot ctx v [a, b] = .ok r) : r = a := by
  unfold memRoot at h
  rw [hop] at h
  cases b with
  | mem m =>
    simp only at h
    split at h
    · split at h
      · cases h
      · cases h; rfl
    · cases h
  | _ => simp only at h; split at h <;> cases h

/-- **A value's evaluation keeps `ArgAv`** of the registers, from a frame whose argument images
avoid activation 0's frame temporaries. -/
theorem argAv_set {tabs : Tables} {f : Func} {env : Env} {fr : Frame}
    (hi : ∀ img ∈ fr.images, BAv Temp0 img) {x : ID} {v : Value} (hv : f.value? x = some v)
    {y : Val} (he : evalValue env (Ctx.make tabs f) fr v = .ok y)
    (hA : ArgAv tabs f (rv fr)) : ArgAv tabs f (rv (fr.set x y)) := by
  intro n a ha
  rw [rv_set]
  split
  · next hh =>
    obtain ⟨rfl, -⟩ := hh
    obtain ⟨n', u, rfl, hu, hc⟩ := argPtrB_cases ha
    rw [hv] at hu; cases hu
    rw [evalValue_of_regs (regs_of_ok he)] at he
    cases hr : evalOp env (Ctx.make tabs f) fr v (v.args.toList.map (rv fr))
        ((Ctx.make tabs f).tys[v.id]?.getD .other) with
    | panic e m => rw [hr] at he; cases he
    | stuck msg => rw [hr] at he; cases he
    | ok r =>
    rw [hr] at he
    cases he
    refine retype_avoids tempU_temp0 _ ?_
    rcases hc with hop | hop | ⟨hop | ⟨hop | hop | hop, hs⟩, h0⟩
    · unfold evalOp at hr
      simp only [hop] at hr
      split at hr
      · exact argVal_avoids₀ hi hr
      · cases hr
    · unfold evalOp at hr
      simp only [hop] at hr
      split at hr
      · exact argVal_avoids₀ hi hr
      · cases hr
    · have ht : termOp v.op = true := by rcases hop with ⟨h | h, -⟩ <;> rw [h] <;> rfl
      rw [evalOp_term ht] at hr
      cases hr
      exact argStep_avoids₀ (.inl hop) _ (rv fr) (hA n' _ h0)
    · have ht : termOp v.op = true := by rw [hop]; rfl
      rw [evalOp_term ht] at hr
      cases hr
      exact argStep_avoids₀ (.inr ⟨.inl hop, hs⟩) _ (rv fr) (hA n' _ h0)
    · have ht : termOp v.op = true := by rw [hop]; rfl
      rw [evalOp_term ht] at hr
      cases hr
      exact argStep_avoids₀ (.inr ⟨.inr hop, hs⟩) _ (rv fr) (hA n' _ h0)
    · unfold evalOp at hr
      simp only [hop] at hr
      rw [args2 hs, List.map_cons, List.map_cons, List.map_nil] at hr
      rw [memRoot_nilCheck hop hr]
      exact hA n' _ h0
  · exact hA n a ha

/-! ## Disjoint pointers -/

/-- **Disjoint pointers** (`disjointB`) address separate bytes where both are pointers, for
valuations whose argument pointers avoid activation 0's frame temporaries (`ArgAv`). -/
theorem disjoint_sep {tabs : Tables} {f : Func} {ρ : ID → Val} (hM : MemAtoms f.value? tabs ρ)
    (hA : ArgAv tabs f ρ) {a b : ID} {n m : Nat} (h : disjointB tabs f a n b m = true)
    {k k' : Nat} {p q : Ptr}
    (ha : (den f.value? tabs ρ k a).asPtrWord = some p)
    (hb : (den f.value? tabs ρ k' b).asPtrWord = some q) : Sep p n q m := by
  unfold disjointB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  obtain ⟨k1, qa, h1, e1⟩ := ptrBase_den 8 a k p ha
  obtain ⟨k2, qb, h2, e2⟩ := ptrBase_den 8 b k' q hb
  -- a frame temporary's pointer and an argument's pointer
  have htemp : ∀ {a b : ID} {k k' : Nat} {p q : Ptr}, tempBaseB tabs f a = true →
      argPtrB tabs f 8 b = true → (den f.value? tabs ρ k a).asPtrWord = some p →
      (den f.value? tabs ρ k' b).asPtrWord = some q → p.blk ≠ q.blk := by
    intro a b k k' p q ht hb' ha hb
    unfold tempBaseB at ht
    obtain ⟨k1, qa, h1, e1⟩ := ptrBase_den 8 a k p ha
    cases hB : baseBlk? tabs f (ptrBase tabs f 8 a).1 with
    | none => rw [hB] at ht; cases ht
    | some B =>
    rw [hB] at ht
    have hq0 := baseBlk_den hM hB h1
    have hB0 : Temp0 B := by
      unfold baseBlk? at hB
      split at hB
      · split at hB
        · rename_i hl
          simp only [Option.map_eq_some_iff] at hB
          obtain ⟨n, -, rfl⟩ := hB
          simp only [Option.any_some] at ht
          unfold frameBlk at ht ⊢
          by_cases hfg : tabs.forgeable n = true
          · simp only [hfg, ↓reduceIte, tempBlk] at ht; cases ht
          · simp only [hfg, Bool.false_eq_true, ↓reduceIte]; exact ⟨n, rfl⟩
        · split at hB
          · split at hB
            · cases hB; simp [tempBlk] at ht
            · cases hB
          · cases hB
      · cases hB
    have hnq := asPtrWord_notU tempU_temp0 (argPtr_den hA 8 b hb' k') hb
    rw [e1, hq0]
    intro he
    exact hnq (he ▸ hB0)
  rcases h with ((⟨hs, hb'⟩ | h) | ⟨ht, hg⟩) | ⟨hg, ht⟩
  · rw [e1, e2, ← baseSame_den hM 8 _ _ hb' h1 h2]
    exact offSep_sep hs
  · split at h
    · rename_i x y hx hy
      rw [bne_iff_ne] at h
      right; right; left
      rw [e1, e2, baseBlk_den hM hx h1, baseBlk_den hM hy h2]
      exact h
    · cases h
  · right; right; left
    exact htemp ht hg ha hb
  · right; right; left
    exact fun he => htemp ht hg hb ha he.symm

end GoFV.Proof.Pass.LoadFwd
