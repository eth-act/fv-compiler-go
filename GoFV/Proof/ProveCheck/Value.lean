import GoFV.Proof.ProveCheck.RngSound

variable [GoFV.SSA.Sem.Addrs]

/-!
# prove's value rewrites are refinements under their facts (issue #24)

`valueOK_ref`: when `valueOK` accepts the rewrite of `fv` into `gv` under assumptions that hold
for `ρ`, then on the same argument values (`Term.den` at any fuel) `gv` evaluates to a
refinement of `fv`: the bounded-shift mark (the amount's range is below the width),
signed → unsigned `Rsh` (the value's range is nonnegative), signed → unsigned `Div`/`Mod` (both
nonnegative), `Ctz` → `CtzNonZero` (argument at least 1), `Mul` → `And` (both arguments 0 or
1), `Slicemask` → `-1` (argument at least 1).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck GoFV.Proof.Term

/-- The shift function of a shift kind. -/
def shF (w : Width) : Nat → BitVec w.bits → Nat → BitVec w.bits
  | 0 => fun x n => x <<< n
  | 1 => fun x n => x.sshiftRight n
  | _ => fun x n => x >>> n

theorem shEval_eq (w a : Width) (k : Nat) (b : Bool) :
    shEval w a k b = Shift.shift w a b (shF w k) := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem shift_cases {w a : Width} {b : Bool} {F : BitVec w.bits → Nat → BitVec w.bits}
    {argv : List Val} (hne : Shift.shift w a b F argv ≠ .poison) :
    ∃ x s, argv = [.int w x, .int a s] ∧ ¬ (b = true ∧ w.bits ≤ s.toNat) := by
  unfold Shift.shift at hne
  split at hne
  · rename_i X S
    cases hx : X.asInt w with
    | none => rw [hx] at hne; exact absurd rfl hne
    | some x =>
      cases hs : S.asInt a with
      | none => rw [hx, hs] at hne; exact absurd rfl hne
      | some s =>
        rw [hx, hs] at hne
        refine ⟨x, s, by rw [asInt_eq hx, asInt_eq hs], fun ⟨hb, hl⟩ => hne ?_⟩
        simp [hb, hl]
  · exact absurd rfl hne

theorem shift_eval {w a : Width} {b : Bool} {F : BitVec w.bits → Nat → BitVec w.bits}
    {x : BitVec w.bits} {s : BitVec a.bits} (hb : ¬ (b = true ∧ w.bits ≤ s.toNat)) :
    Shift.shift w a b F [.int w x, .int a s] = .int w (F x (min s.toNat w.bits)) := by
  simp only [Shift.shift, Val.asInt_int]
  rw [if_neg (by simpa using hb)]

theorem msb_false_of {n : Nat} {x : BitVec n} (h : 0 ≤ x.toInt) : x.msb = false := by
  have := BitVec.msb_eq_toInt (x := x)
  rw [this]; simp; omega

theorem int1_ref {w : Width} {f g : BitVec w.bits → Val} {argv : List Val} (P : BitVec w.bits → Prop)
    (hP : ∀ v x, argv = [v] → v = .int w x → P x) (hfg : ∀ x, P x → Sem.Refines (f x) (g x)) :
    Sem.Refines (Sem.int1 w f argv) (Sem.int1 w g argv) := by
  unfold Sem.int1
  split
  · rename_i v
    cases hx : v.asInt w with
    | none => exact .poison _
    | some x => exact hfg x (hP v x rfl (asInt_eq hx))
  · exact .poison _

theorem int2_ref {w : Width} {f g : BitVec w.bits → BitVec w.bits → Val} {argv : List Val}
    (P : BitVec w.bits → Prop) (hP : ∀ v ∈ argv, ∀ x, v = .int w x → P x)
    (hfg : ∀ x y, P x → P y → Sem.Refines (f x y) (g x y)) :
    Sem.Refines (Sem.int2 w f argv) (Sem.int2 w g argv) := by
  unfold Sem.int2
  split
  · rename_i u v
    cases hx : u.asInt w with
    | none => exact .poison _
    | some x =>
      cases hy : v.asInt w with
      | none => exact .poison _
      | some y =>
        exact hfg x y (hP u List.mem_cons_self x (asInt_eq hx))
          (hP v (List.mem_cons_of_mem _ List.mem_cons_self) y (asInt_eq hy))
  · exact .poison _

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {A : Asm}

/-- The arguments' ranges. -/
theorem argRng (h : AsmHolds D tabs ρ A) {m : Nat} {a : ID} {w : Width} {y : BitVec w.bits}
    (hy : den D tabs ρ m a = .int w y) : (rng D tabs A rngFuel w a).Mem y :=
  rng_sound h rngFuel w a m y hy

/-- A property of every argument's integer value from a check on every argument's range. -/
theorem argsP (h : AsmHolds D tabs ρ A) {m : Nat} {args : Array ID} {w : Width}
    {chk : Rng → Bool} {P : BitVec w.bits → Prop} (hP : ∀ r y, r.Mem y → chk r = true → P y)
    (hc : args.all (fun a => chk (rng D tabs A rngFuel w a)) = true) :
    ∀ v ∈ args.toList.map (den D tabs ρ m), ∀ x, v = .int w x → P x := by
  intro v hv x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
  rw [Array.all_eq_true'] at hc
  exact hP _ _ (argRng h hx) (hc a (Array.mem_toList_iff.1 ha))

theorem mul_eq_and {n : Nat} (hn : 0 < n) {x y : BitVec n} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    x * y = x &&& y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_and]
  have h1 : x.toNat = 0 ∨ x.toNat = 1 := by omega
  have h2 : y.toNat = 0 ∨ y.toNat = 1 := by omega
  have hl := x.isLt
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> simp [hn]

/-- **A value rewrite refines on equal argument values.** -/
theorem valueOK_ref (h : AsmHolds D tabs ρ A) {fv gv : Value} (hv : valueOK D tabs A fv gv = true)
    (m : Nat) :
    Sem.Refines
      (evalPure fv.op (tabs.ty fv.type) fv.auxInt fv.aux (fv.args.toList.map (den D tabs ρ m)))
      (evalPure gv.op (tabs.ty fv.type) gv.auxInt gv.aux (gv.args.toList.map (den D tabs ρ m))) := by
  unfold valueOK at hv
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨⟨-, hax⟩, hv⟩ := hv
  rw [hax]
  split at hv
  · -- shifts
    rename_i w a kf w' a' kg hf hg
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨⟨hargs, rfl⟩, rfl⟩, hk⟩, hai⟩ := hv
    rw [shTab_eval hf, shTab_eval hg, shEval_eq, shEval_eq, hargs]
    by_cases hne : Shift.shift w a (fv.auxInt == 1) (shF w kf) (gv.args.toList.map (den D tabs ρ m))
      = .poison
    · rw [hne]; exact .poison _
    obtain ⟨x, s, hl, hb⟩ := shift_cases hne
    rw [hl, shift_eval hb]
    obtain ⟨hx0, hs0⟩ := map_two hl
    have hbg : ¬ ((gv.auxInt == 1) = true ∧ w.bits ≤ s.toNat) := by
      rintro ⟨hb1, hle⟩
      rcases hai with e | ⟨e1, e2⟩
      · rw [e] at hb1; exact hb ⟨hb1, hle⟩
      · rw [← hargs] at hs0
        obtain ⟨-, m2, -, -⟩ := argRng h hs0
        omega
    rw [shift_eval hbg]
    have hF : shF w kf x (min s.toNat w.bits) = shF w kg x (min s.toNat w.bits) := by
      rcases hk with e | ⟨⟨rfl, rfl⟩, hnn⟩
      · rw [e]
      · rw [← hargs] at hx0
        obtain ⟨-, -, m3, -⟩ := argRng h hx0
        exact BitVec.sshiftRight_eq_of_msb_false (msb_false_of (by omega))
    rw [hF]; exact .int _ _
  · split at hv
    · -- signed → unsigned division / remainder
      rename_i w hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      obtain ⟨⟨-, hargs⟩, hnn⟩ := hv
      rw [← hargs]
      have hP := argsP (m := m) (P := fun y : BitVec w.bits => y.msb = false)
        (chk := fun r => decide (r.slo ≥ 0))
        (fun r y hr hc => msb_false_of (by
          obtain ⟨-, -, m3, -⟩ := hr; simp only [decide_eq_true_eq] at hc; omega)) (h := h) hnn
      cases opTab_mem hk with
      | div hf hg =>
        rw [hf, hg]
        refine int2_ref _ hP fun x y hx hy => ?_
        by_cases hy0 : y = 0
        · simp only [hy0, ite_true]; exact .poison _
        · simp only [hy0, ite_false]
          split
          · exact .poison _
          · rw [BitVec.sdiv_eq, hx, hy]; exact .int _ _
      | mod hf hg =>
        rw [hf, hg]
        refine int2_ref _ hP fun x y hx hy => ?_
        by_cases hy0 : y = 0
        · simp only [hy0, ite_true]; exact .poison _
        · simp only [hy0, ite_false]
          split
          · exact .poison _
          · rw [BitVec.srem_eq, hx, hy]; exact .int _ _
    · -- `Ctz` → `CtzNonZero`
      rename_i w hk
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
      obtain ⟨⟨hai, hargs⟩, hlo⟩ := hv
      rw [← hargs]
      cases opTab_mem hk with
      | ctz hf hg =>
        rw [hf, hg]
        simp only [Sem.Int.ctz]
        refine int1_ref (fun y : BitVec w.bits => y ≠ 0) (fun v x hl hx => ?_) fun x hx => ?_
        · obtain ⟨m1, -, -, -⟩ := argRng h (hx ▸ map_one hl)
          intro e; rw [e] at m1; simp at m1; omega
        · simp only [Bool.false_and, Bool.false_eq_true, ite_false, Bool.true_and]
          rw [if_neg (by simpa using hx)]; exact .refl _
    · -- `Mul` → `And`
      rename_i w hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      obtain ⟨⟨-, hargs⟩, hle⟩ := hv
      rw [← hargs]
      have hP := argsP (m := m) (P := fun y : BitVec w.bits => y.toNat ≤ 1)
        (chk := fun r => decide (r.uhi ≤ 1))
        (fun r y hr hc => by
          obtain ⟨-, m2, -, -⟩ := hr; simp only [decide_eq_true_eq] at hc; omega) (h := h) hle
      cases opTab_mem hk with
      | mul hf hg =>
        rw [hf, hg]
        refine int2_ref _ hP fun x y hx hy => ?_
        rw [mul_eq_and (Width.one_le w) hx hy]; exact .int _ _
    · -- `Slicemask` → `-1`
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      obtain ⟨⟨⟨hop, -⟩, hai⟩, hw⟩ := hv
      split at hw
      · rename_i w hwT
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
        obtain ⟨hgo, hlo⟩ := hw
        rw [hop, hai]
        have hs : ∀ argv, evalPure .Slicemask (tabs.ty fv.type) fv.auxInt gv.aux argv =
            Sem.Int.slicemask w argv := fun argv => by
          show (match (tabs.ty fv.type).width? with
            | some w => Sem.Int.slicemask w argv | none => .poison) = _
          rw [hwT]
        rw [hs]
        by_cases hne : Sem.Int.slicemask w (fv.args.toList.map (den D tabs ρ m)) = .poison
        · rw [hne]; exact .poison _
        obtain ⟨v, x, hl, rfl, he⟩ := int1_eq rfl hne
        obtain ⟨m1, -, -, -⟩ := argRng h (map_one hl)
        have hx0 : x ≠ 0 := fun e => by rw [e] at m1; simp at m1; omega
        unfold Sem.Int.slicemask
        rw [← he]
        split
        · exact .poison _
        all_goals first
          | contradiction
          | (rcases hgo with ⟨hg, rfl⟩ | ⟨hg, rfl⟩ <;> rw [hg] <;> exact .int _ _)
      · cases hw

/-- The ops of a value rewrite are not table-evaluated (`Rules.frameOp`): table entries, or
`Slicemask` → `Const64`/`Const32`. -/
theorem valueOK_frame {fv gv : Value} (hv : valueOK D tabs A fv gv = true) :
    GoFV.Proof.Rules.frameOp fv.op = false ∧ GoFV.Proof.Rules.frameOp gv.op = false := by
  unfold valueOK at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨-, hv⟩ := hv
  have hsh : ∀ p ∈ shTab, GoFV.Proof.Rules.frameOp p.1 = false := by decide
  have hop : ∀ p ∈ opTab, GoFV.Proof.Rules.frameOp p.1.1 = false ∧
      GoFV.Proof.Rules.frameOp p.1.2 = false := by decide
  split at hv
  · rename_i hf hg
    exact ⟨hsh _ (mem_of_lookup hf), hsh _ (mem_of_lookup hg)⟩
  · split at hv
    · rename_i hk; exact hop _ (mem_of_lookup hk)
    · rename_i hk; exact hop _ (mem_of_lookup hk)
    · rename_i hk; exact hop _ (mem_of_lookup hk)
    · simp only [Bool.and_eq_true, beq_iff_eq] at hv
      obtain ⟨⟨⟨hs, -⟩, -⟩, hw⟩ := hv
      split at hw
      · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hw
        rw [hs]
        rcases hw with ⟨hg, -⟩ | ⟨hg, -⟩ <;> rw [hg] <;> exact ⟨rfl, rfl⟩
      · cases hw

/-- `valueOK_ref` for term-node values (`Rules.opVal`). -/
theorem valueOK_refT (h : AsmHolds D tabs ρ A) {fv gv : Value} (hv : valueOK D tabs A fv gv = true)
    (m : Nat) :
    Sem.Refines
      (GoFV.Proof.Rules.opVal tabs fv.op (tabs.ty fv.type) fv.auxInt fv.aux
        (fv.args.toList.map (den D tabs ρ m)))
      (GoFV.Proof.Rules.opVal tabs gv.op (tabs.ty fv.type) gv.auxInt gv.aux
        (gv.args.toList.map (den D tabs ρ m))) := by
  obtain ⟨h1, h2⟩ := valueOK_frame hv
  rw [GoFV.Proof.Rules.opVal_pure h1, GoFV.Proof.Rules.opVal_pure h2]
  exact valueOK_ref h hv m

end

end GoFV.Proof.ProveCheck
