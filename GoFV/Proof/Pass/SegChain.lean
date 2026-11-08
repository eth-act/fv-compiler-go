import GoFV.Proof.Pass.SegSound
import GoFV.Proof.PtrAddr

variable [GoFV.SSA.Sem.Addrs]

/-!
# Segments: chains of stores over a zeroed region (issue #151)

`chainSeg_sound` discharges `SegSound` for the chain segments (`generic.rules:1833` family,
`RewriteCheck.chainSeg?`): in `f`, `x = Store op1 d1 m2`, …, `mk = Store opk dk z` over
`z = Zero [n] p m0`; in `g`, `x = Store op1 d1 n2` over fresh `n2 = Store op2 d2 n3`, …,
`nk = Store opk dk m0`, every `opj` a pointer-shaped `OffPtr` of `p` (up to copies), the stores
tiling `[0, n)`. The source's registers give `x`'s memory as `writes P Z ws` over the zeroed
memory `Z` (`P` the pointer word of `p`'s register, `Val.asPtrWord`; the `OffPtr`s hold words of
`P` plus their offsets), with `Tiles 0 n ws`; by `writes_over_zero_eq` it is `writes P M0 ws`,
which the target's fresh stores and anchor compute from `M0`, bottom first.
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE.Mem (Avail)
open GoFV.Proof.AtomSim (Reg rv rv_of evalValue_of_regs)

/-! ## The chains of the validator -/

/-- `ss` are `Store`s of `f` from `m` down their memory arguments (first first), over `z`. -/
def SChain (f : Func) : ID → List ID → ID → Prop
  | m, [], z => m = z
  | m, s :: ss, z => s = m ∧ ∃ sv, f.value? m = some sv ∧ sv.op = .Store ∧ sv.args.size = 3 ∧
      SChain f sv.args[2]! ss z

/-- `ts` are values of `g` but not of `f` from `m` down their last arguments, over `m0`. -/
def FChain (f g : Func) : ID → List ID → ID → Prop
  | m, [], m0 => m = m0
  | m, t :: ts, m0 => t = m ∧ f.value? m = none ∧ ∃ tv, g.value? m = some tv ∧
      FChain f g (lastArg tv) ts m0

theorem storesF_chain {f : Func} : ∀ {k : Nat} {m : ID} {ss : List ID} {z : ID},
    storesF f k m = some (ss, z) → SChain f m ss z ∧ ss.length = k
  | 0, m, ss, z, h => by
    simp only [storesF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | k + 1, m, ss, z, h => by
    unfold storesF at h
    cases hm : f.value? m with
    | none => rw [hm] at h; cases h
    | some s =>
      rw [hm] at h
      simp only at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        cases hr : storesF f k s.args[2]! with
        | none => rw [hr] at h; cases h
        | some r =>
          obtain ⟨r1, r2⟩ := r
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := storesF_chain hr
          exact ⟨⟨rfl, s, hm, hc.1, hc.2, h1⟩, by simp [h2]⟩
      · cases h

theorem freshChain_chain {f g : Func} : ∀ {k : Nat} {m : ID} {ns : List ID} {m0 : ID},
    freshChain f g k m = (ns, m0) → FChain f g m ns m0
  | 0, m, ns, m0, h => by
    simp only [freshChain, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | k + 1, m, ns, m0, h => by
    unfold freshChain at h
    split at h
    · rename_i s hf hg
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hf, s, hg, freshChain_chain rfl⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

theorem SChain.store {f : Func} : ∀ {m z : ID} {ss : List ID}, SChain f m ss z →
    ∀ s ∈ ss, ∃ sv, f.value? s = some sv ∧ sv.op = .Store
  | _, _, [], _, s, hs => absurd hs List.not_mem_nil
  | _, _, _ :: _, ⟨rfl, sv, hv, hop, _, hc⟩, s, hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨sv, hv, hop⟩
    · exact hc.store s hs

/-! ## Tilings -/

private theorem segTiles_append {tabs : Tables} {f : Func} {p : ID} : ∀ (o : Nat) (l1 l2 : List Value)
    (n : Nat), segTiles tabs f p o (l1 ++ l2) n = true →
    ∃ mid, segTiles tabs f p o l1 mid = true ∧ segTiles tabs f p mid l2 n = true
  | o, [], l2, n, h => ⟨o, by simp [segTiles], h⟩
  | o, s :: l1, l2, n, h => by
    rw [List.cons_append, segTiles] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h4⟩ := h
    obtain ⟨mid, h5, h6⟩ := segTiles_append _ l1 l2 n h4
    exact ⟨mid, by rw [segTiles]; simp only [Bool.and_eq_true]; exact ⟨h1, h5⟩, h6⟩

/-- One store of a tiling: positive size, at an `OffPtr` of `p` (up to copies) by `o` of pointer
shape, ending at `n`. -/
private theorem segTiles_one {tabs : Tables} {f : Func} {p : ID} {o n : Nat} {s : Value}
    (h : segTiles tabs f p o [s] n = true) :
    0 < (auxTy tabs s.aux).size ∧ s.args.size = 3 ∧ o + (auxTy tabs s.aux).size = n ∧
      ∃ op, f.value? s.args[0]! = some op ∧ op.op = .OffPtr ∧ op.args.size = 1 ∧
        op.auxInt.toInt = (o : Int) ∧ isPtrTy (tabs.ty op.type) = true ∧
        copyEnd tabs f.valueTab f.valueTab.size op.args[0]! =
          copyEnd tabs f.valueTab f.valueTab.size p := by
  rw [segTiles] at h
  simp only [segTiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h3⟩, hm⟩, hn⟩ := h
  refine ⟨h0, h3, hn, ?_⟩
  cases hv : f.value? s.args[0]! with
  | none => rw [hv] at hm; cases hm
  | some op =>
    rw [hv] at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨⟨⟨h1, h2⟩, h4⟩, hty⟩, h5⟩ := hm
    exact ⟨op, rfl, h1, h2, h4, hty, h5⟩

private theorem Tiles.append : ∀ {lo mid n : Nat} {w1 w2 : List (Nat × Array Byte)},
    Tiles lo mid w1 → Tiles mid n w2 → Tiles lo n (w1 ++ w2)
  | lo, mid, n, [], w2, h1, h2 => by
    have : lo = mid := h1
    subst this
    exact h2
  | _, _, _, (_, _) :: _, _, ⟨ho, hb, ht⟩, h2 => ⟨ho, hb, Tiles.append ht h2⟩

theorem writes_append (P : Ptr) : ∀ (m : Mem) (w1 w2 : List (Nat × Array Byte)),
    writes P m (w1 ++ w2) = (writes P m w1).bind (writes P · w2)
  | m, [], w2 => rfl
  | m, (o, bs) :: w1, w2 => by
    rw [List.cons_append, writes, writes]
    cases m.write (P.add (BitVec.ofNat 64 o)) bs with
    | none => rfl
    | some m1 => exact writes_append P m1 w1 w2

theorem writes_one (P : Ptr) (m : Mem) (o : Nat) (bs : Array Byte) :
    writes P m [(o, bs)] = m.write (P.add (BitVec.ofNat 64 o)) bs := by
  rw [writes]
  cases m.write (P.add (BitVec.ofNat 64 o)) bs <;> rfl

theorem writes_snoc {P : Ptr} {m W : Mem} {ws : List (Nat × Array Byte)} {o : Nat}
    {bs : Array Byte} (h : writes P m (ws ++ [(o, bs)]) = some W) :
    ∃ W1, writes P m ws = some W1 ∧ W1.write (P.add (BitVec.ofNat 64 o)) bs = some W := by
  rw [writes_append] at h
  cases h1 : writes P m ws with
  | none => rw [h1] at h; cases h
  | some W1 => rw [h1, Option.bind_some, writes_one] at h; exact ⟨W1, rfl, h⟩

/-! ## Evaluations -/

theorem retype_mem_eq {t : Ty} {M M' : Mem} (h : (Val.mem M).retype t = .mem M') :
    t = .mem ∧ M = M' := by
  cases t <;> simp [Val.retype] at h ⊢
  exact h

theorem lastArg_three {w : Value} (h : w.args.size = 3) : lastArg w = w.args[2]! := by
  rw [lastArg, CSE.Mem.args_three h]
  simp

/-- A `Store`'s evaluation from its argument registers: a write at its address word. -/
theorem store_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {q d m : ID} {qv xv mv y : Val}
    (hop : v.op = .Store) (ha : v.args = #[q, d, m]) (hq : fr.regs[q]? = some (some qv))
    (hd : fr.regs[d]? = some (some xv)) (hm : fr.regs[m]? = some (some mv))
    (h : evalValue env ctx fr v = .ok y) :
    ∃ Q M M', qv.asPtrWord = some Q ∧ mv = .mem M ∧
      M.write Q (encode (auxTy ctx.tabs v.aux) xv) = some M' ∧
      y = (Val.mem M').retype (ctx.tys[v.id]?.getD .other) := by
  obtain ⟨argv, r, hargs, ho, rfl⟩ := CSE.Mem.evalValue_ok h
  have : argv = [qv, xv, mv] := CSE.Mem.map_some_inj (by rw [← hargs, ha]; simp [hq, hd, hm])
  subst this
  rw [CSE.Mem.evalOp_memRoot (.inl hop)] at ho
  obtain ⟨Q, M, M', hQ, rfl, hw, rfl⟩ := StructStore.memRoot_store_ok hop ho
  exact ⟨Q, M, M', hQ, rfl, hw, rfl⟩

/-- A `Store` evaluates to its write at its address word. -/
theorem store_eval {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {q d m : ID} {Q : Ptr}
    {qv xv : Val} {M M' : Mem}
    (hop : v.op = .Store) (ha : v.args = #[q, d, m]) (hq : fr.regs[q]? = some (some qv))
    (hQ : qv.asPtrWord = some Q)
    (hd : fr.regs[d]? = some (some xv)) (hm : fr.regs[m]? = some (some (.mem M)))
    (hw : M.write Q (encode (auxTy ctx.tabs v.aux) xv) = some M') :
    evalValue env ctx fr v = .ok ((Val.mem M').retype (ctx.tys[v.id]?.getD .other)) := by
  rw [evalValue_of_regs (fun a ha' => by
      rw [ha] at ha'
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl | rfl
      · exact ⟨_, hq⟩
      · exact ⟨_, hd⟩
      · exact ⟨_, hm⟩), CSE.Mem.evalOp_memRoot (.inl hop)]
  have hl : v.args.toList.map (rv fr) = [qv, xv, .mem M] := by
    rw [ha]; simp [rv_of hq, rv_of hd, rv_of hm]
  rw [hl]
  simp only [memRoot, hop, hQ, hw, writeRes]
  rfl

/-- A `Zero`'s evaluation from its argument registers: a write at its address word. -/
theorem zero_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {q m : ID} {qv mv y : Val}
    (hop : v.op = .Zero) (ha : v.args = #[q, m]) (hq : fr.regs[q]? = some (some qv))
    (hm : fr.regs[m]? = some (some mv)) (h : evalValue env ctx fr v = .ok y) :
    ∃ Q M M', qv.asPtrWord = some Q ∧ mv = .mem M ∧
      M.write Q (Array.replicate v.auxInt.toInt.toNat (.b 0)) = some M' ∧
      y = (Val.mem M').retype (ctx.tys[v.id]?.getD .other) := by
  obtain ⟨argv, r, hargs, ho, rfl⟩ := CSE.Mem.evalValue_ok h
  have : argv = [qv, mv] := CSE.Mem.map_some_inj (by rw [← hargs, ha]; simp [hq, hm])
  subst this
  rw [CSE.Mem.evalOp_memRoot (.inr hop)] at ho
  unfold memRoot at ho
  rw [hop] at ho
  cases mv <;> simp only at ho <;> try (split at ho <;> cases ho)
  rename_i M
  cases hp : qv.asPtrWord with
  | none => rw [hp] at ho; cases ho
  | some Q =>
    rw [hp] at ho; simp only at ho
    obtain ⟨M', hw, rfl⟩ := CSE.Mem.writeRes_ok ho
    exact ⟨Q, M, M', rfl, rfl, hw, rfl⟩

section
variable {env : Env} {tabs : Tables} {f g : Func} {S : Frame} {A : ID → Prop}

/-- An `OffPtr` by `o` of pointer shape whose argument holds `p`'s register, `p` holding a word
of the pointer `P`, holds a word of `P + o` if it holds a pointer word. -/
theorem offPtr_reg_of (H : Avail env tabs f S A)
    (hid : ∀ z v, A z → f.value? z = some v → v.id = z) {q pz : ID} {opv : Value} {P Q : Ptr}
    {pv qv : Val} {o : Nat} (hA : A q) (hq : f.value? q = some opv)
    (hop : opv.op = .OffPtr) (hsz : opv.args.size = 1) (hai : opv.auxInt.toInt = (o : Int))
    (hty : isPtrTy (tabs.ty opv.type) = true)
    (hcP : S.regs[opv.args[0]!]? = S.regs[pz]?)
    (hP : S.regs[pz]? = some (some pv)) (hpv : pv.asPtrWord = some P)
    (hQ : S.regs[q]? = some (some qv)) (hqv : qv.asPtrWord = some Q) :
    Q = P.add (BitVec.ofNat 64 o) := by
  have hargs : opv.args = #[opv.args[0]!] := StructStore.args1 hsz
  generalize hc : opv.args[0]! = c at hcP hargs
  rw [hP] at hcP
  obtain ⟨v', y, hv', hy, hev⟩ := H.val q hA
  rw [hq] at hv'
  cases hv'
  rw [hQ] at hy
  cases hy
  have hev := hev (by rw [hop]; decide)
  rw [evalValue_of_regs (fun b hb => by
    rw [hargs] at hb; simp at hb; subst hb; exact ⟨_, hcP⟩)] at hev
  have hl : opv.args.toList.map (rv S) = [pv] := by rw [hargs]; simp [rv_of hcP]
  rw [hl, show ∀ ty, evalOp env (Ctx.make tabs f) S opv [pv] ty =
      .ok (evalPure .OffPtr ty opv.auxInt opv.aux [pv]) from
    fun ty => by simp only [evalOp, frameVal, hop]; rfl, StructStore.evalPure_offPtr,
    hid q opv hA hq, Proof.tys_of_value hq, Option.getD_some] at hev
  simp only [pure, Res.bind, bind] at hev
  cases hev
  revert hqv hty
  generalize tabs.ty opv.type = ty
  intro hty hqv
  cases ty <;> simp [isPtrTy] at hty
  rw [PtrOps.offPtr_retype_ptr, PtrOps.offPtr_asPtrWord, hpv, Option.bind_some, hai,
    BitVec.ofInt_natCast, Ptr.step?] at hqv
  split at hqv
  · exact (Option.some.inj hqv).symm
  · cases hqv

/-- An `OffPtr` by `o` of pointer shape of a value reaching `p` through copies, `p` holding a
word of the pointer `P`, holds a word of `P + o` if it holds a pointer word. -/
theorem offPtr_reg (H : Avail env tabs f S A) (hT : Proof.Typed (Ctx.make tabs f) S)
    (hid : ∀ z v, A z → f.value? z = some v → v.id = z) {q pz : ID} {opv : Value} {P Q : Ptr}
    {pv qv : Val} {o : Nat} (hA : A q) (hpA : A pz) (hq : f.value? q = some opv)
    (hop : opv.op = .OffPtr) (hsz : opv.args.size = 1) (hai : opv.auxInt.toInt = (o : Int))
    (hty : isPtrTy (tabs.ty opv.type) = true)
    (hce : copyEnd tabs f.valueTab f.valueTab.size opv.args[0]! =
      copyEnd tabs f.valueTab f.valueTab.size pz)
    (hP : S.regs[pz]? = some (some pv)) (hpv : pv.asPtrWord = some P)
    (hQ : S.regs[q]? = some (some qv)) (hqv : qv.asPtrWord = some Q) :
    Q = P.add (BitVec.ofNat 64 o) := by
  have hargs : opv.args = #[opv.args[0]!] := StructStore.args1 hsz
  have hcA : A opv.args[0]! := H.cl q opv hA hq (by rw [hop]; decide) _ (by rw [hargs]; simp)
  have h1 := (StructStore.copy_reg H hT hid f.valueTab.size hcA
    (StructStore.copyReach_copyEnd _ f.valueTab.size _)).2
  have h2 := (StructStore.copy_reg H hT hid f.valueTab.size hpA
    (StructStore.copyReach_copyEnd _ f.valueTab.size pz)).2
  rw [hce, h2] at h1
  exact offPtr_reg_of H hid hA hq hop hsz hai hty h1.symm hP hpv hQ hqv

/-- One store of the source chain at offset `mid`: its pointer holds a word of `P + mid`, its
memory argument a memory, and it holds the write of its value there. -/
private theorem level_src (H : Avail env tabs f S A) (hT : Proof.Typed (Ctx.make tabs f) S)
    (hid : ∀ z v, A z → f.value? z = some v → v.id = z) {pz : ID} {P : Ptr} {pv : Val} (hpA : A pz)
    (hP : S.regs[pz]? = some (some pv)) (hpv : pv.asPtrWord = some P) {s : ID} {sv : Value}
    (hA : A s) (hs : f.value? s = some sv) (hop : sv.op = .Store) {mid o : Nat}
    (ht : segTiles tabs f pz mid [sv] o = true) :
    ∃ qv xv M1 M2, sv.args = #[sv.args[0]!, sv.args[1]!, sv.args[2]!] ∧ A sv.args[0]! ∧
      A sv.args[1]! ∧ A sv.args[2]! ∧
      S.regs[sv.args[0]!]? = some (some qv) ∧ qv.asPtrWord = some (P.add (BitVec.ofNat 64 mid)) ∧
      S.regs[sv.args[1]!]? = some (some xv) ∧ S.regs[sv.args[2]!]? = some (some (.mem M1)) ∧
      M1.write (P.add (BitVec.ofNat 64 mid)) (encode (auxTy tabs sv.aux) xv) = some M2 ∧
      S.regs[s]? = some (some ((Val.mem M2).retype (tabs.ty sv.type))) ∧
      Tiles mid o [(mid, encode (auxTy tabs sv.aux) xv)] := by
  obtain ⟨h0, h3, hn, opv, hq, hoff, hsz1, hai, hty, hce⟩ := segTiles_one ht
  have ha := CSE.Mem.args_three h3
  have hcl := H.cl s sv hA hs (by rw [hop]; decide)
  have hA0 := hcl sv.args[0]! (by rw [ha]; simp)
  have hA1 := hcl sv.args[1]! (by rw [ha]; simp)
  have hA2 := hcl sv.args[2]! (by rw [ha]; simp)
  obtain ⟨_, qv, -, hqv, -⟩ := H.val _ hA0
  obtain ⟨_, xv, -, hxv, -⟩ := H.val _ hA1
  obtain ⟨_, mv, -, hmv, -⟩ := H.val _ hA2
  obtain ⟨v', y, hv', hy, hev⟩ := H.val s hA
  rw [hs] at hv'
  cases hv'
  obtain ⟨Q, M1, M2, hQ, rfl, hw, rfl⟩ :=
    store_ok hop ha hqv hxv hmv (hev (by rw [hop]; decide))
  have hQe := offPtr_reg H hT hid hA0 hpA hq hoff hsz1 hai hty hce hP hpv hqv hQ
  subst hQe
  rw [hid s sv hA hs, Proof.tys_of_value hs, Option.getD_some] at hy
  refine ⟨qv, xv, M1, M2, ha, hA0, hA1, hA2, hqv, hQ, hxv, hmv, hw, hy, rfl, ?_, ?_⟩
  · rw [Sem.encode_size]; exact h0
  · show mid + _ = o
    rw [Sem.encode_size]; exact hn

/-- **The chain below the anchor**: if the source's chain from `s` (over `z`) evaluated to
`M`, the stores' writes `ws` take the zeroed memory `Z` to `M`, tile `[0, o)`, and the target's
fresh chain from `t` (over `m0`) evaluates to their writes over `M0`. -/
private theorem chain_below (H : Avail env tabs f S A) (hT : Proof.Typed (Ctx.make tabs f) S)
    (hid : ∀ z v, A z → f.value? z = some v → v.id = z) {pz z m0 b : ID} {P : Ptr} {pv : Val}
    {Z M0 : Mem} (hpA : A pz) (hP : S.regs[pz]? = some (some pv)) (hpv : pv.asPtrWord = some P)
    (hm0A : A m0)
    (hm0 : S.regs[m0]? = some (some (.mem M0)))
    (hz : ∀ M, S.regs[z]? = some (some (.mem M)) → M = Z) :
    ∀ (fs ns : List ID) (s t : ID) (o : Nat) (M : Mem), SChain f s fs z → FChain f g t ns m0 →
      fs.length = ns.length → (∀ n ∈ ns, ∀ v, g.value? n = some v → v.id = n) →
      (fs.zip ns).all (fun (a, c) => match f.value? a, g.value? c with
        | some sa, some sb => segStoreSame b sa sb
        | _, _ => false) = true →
      segTiles tabs f pz 0 (fs.filterMap f.value?).reverse o = true →
      S.regs[s]? = some (some (.mem M)) → A s →
      ∃ ws, writes P Z ws = some M ∧ Tiles 0 o ws ∧ ∀ W, writes P M0 ws = some W →
        ∀ Fr : Frame, (∀ a, A a → Fr.regs[a]? = S.regs[a]?) → g.valueTab.size ≤ Fr.regs.size →
        ∃ Fr', evalAll env (Ctx.make tabs g) Fr ns.reverse = .ok Fr' ∧
          Fr'.regs[t]? = some (some (.mem W)) ∧ (∀ a, A a → Fr'.regs[a]? = S.regs[a]?) ∧
          g.valueTab.size ≤ Fr'.regs.size
  | [], ns, s, t, o, M, hsc, hfc, hlen, _, _, hst, hM, _ => by
    cases ns with
    | cons _ _ => cases hlen
    | nil =>
    have hs : s = z := hsc
    have ht : t = m0 := hfc
    subst hs ht
    have ho : o = 0 := by
      simp only [List.filterMap_nil, List.reverse_nil, segTiles, beq_iff_eq] at hst
      exact hst.symm
    subst ho
    obtain rfl := hz M hM
    refine ⟨[], rfl, rfl, fun W hW Fr hag hsz => ?_⟩
    cases hW
    exact ⟨Fr, rfl, by rw [hag _ hm0A, hm0], hag, hsz⟩
  | s' :: fs1, ns, s, t, o, M, hsc, hfc, hlen, hgid, hzip, hst, hM, hA => by
    cases ns with
    | nil => cases hlen
    | cons t' ns1 =>
    obtain ⟨hs', sv, hs, hop, hsz3, hsc1⟩ := hsc
    subst s'
    obtain ⟨ht', hft, tv, htv, hfc1⟩ := hfc
    subst t'
    simp only [List.zip_cons_cons, List.all_cons, hs, htv, Bool.and_eq_true] at hzip
    obtain ⟨hss, hzip1⟩ := hzip
    rw [List.filterMap_cons_some hs, List.reverse_cons] at hst
    obtain ⟨mid, hst1, hst2⟩ := segTiles_append _ _ _ _ hst
    obtain ⟨qv, xv, M1, M2, ha, hA0, hA1, hA2, hq, hqw, hx, hm1, hw, hy, htile⟩ :=
      level_src H hT hid hpA hP hpv hA hs hop hst2
    rw [hM] at hy
    obtain ⟨hty, rfl⟩ := retype_mem_eq (Option.some.inj (Option.some.inj hy)).symm
    obtain ⟨ws1, hz1, ht1, htg⟩ := chain_below H hT hid hpA hP hpv hm0A hm0 hz fs1 ns1 sv.args[2]!
      (lastArg tv) mid M1 hsc1 hfc1 (by simpa using hlen)
      (fun n hn => hgid n (List.mem_cons_of_mem _ hn)) hzip1 hst1 hm1 hA2
    refine ⟨ws1 ++ [(mid, encode (auxTy tabs sv.aux) xv)], ?_, Tiles.append ht1 htile, ?_⟩
    · rw [writes_append, hz1, Option.bind_some, writes_one, hw]
    intro W hW Fr hag hsz
    obtain ⟨W1, hW1, hw1⟩ := writes_snoc hW
    obtain ⟨Fr1, he1, hr1, hag1, hsz1⟩ := htg W1 hW1 Fr hag hsz
    -- the target's store `t`
    unfold segStoreSame at hss
    simp only [Bool.and_eq_true, beq_iff_eq] at hss
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, htop⟩, -⟩, htsz⟩, haux⟩, htype⟩, h0⟩, h1⟩, -⟩, -⟩ := hss
    have hta : tv.args = #[sv.args[0]!, sv.args[1]!, lastArg tv] := by
      rw [lastArg_three htsz, ← h0, ← h1]; exact CSE.Mem.args_three htsz
    have hev := store_eval (env := env) (ctx := Ctx.make tabs g) htop hta
      (by rw [hag1 _ hA0]; exact hq) hqw (by rw [hag1 _ hA1]; exact hx) hr1
      (by rw [show (Ctx.make tabs g).tabs = tabs from rfl, haux]; exact hw1)
    rw [hgid t (List.mem_cons_self) tv htv, Proof.tys_of_value htv, Option.getD_some, htype,
      hty] at hev
    have htlt : t < Fr1.regs.size := Nat.lt_of_lt_of_le (CheckFacts.lt_of_value? htv) hsz1
    refine ⟨Fr1.set t (.mem W), ?_, Proof.Frame.set_regs_self htlt, fun a ha' => ?_, ?_⟩
    · rw [List.reverse_cons, Proof.evalAll_append, he1]
      dsimp only
      rw [Proof.evalAll_cons]
      simp only [Proof.stepV, show (Ctx.make tabs g).f = g from rfl, htv, hev]
      rfl
    · have hne : t ≠ a := by
        rintro rfl
        obtain ⟨_, _, hv, -⟩ := H.val t ha'
        rw [hft] at hv
        cases hv
      rw [Proof.Frame.set_regs_ne hne, hag1 a ha']
    · simpa [Frame.set] using hsz1

end

/-! ## The obligation -/

private theorem prio_store : prio .Store ≠ 0 := by decide
private theorem prio_zero : prio .Zero ≠ 0 := by decide

/-- **Chain segments are sound**: the target's fresh stores and anchor evaluate from the source
frame, and its anchor holds the source's. -/
theorem chainSeg_sound {tabs : Tables} {f g : Func} {x : ID} {fv gv : Value} {D N : List ID}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (h : chainSeg? tabs f g x fv gv = some (D, N))
    (hgid : ∀ n ∈ N ++ [x], ∀ v, g.value? n = some v → v.id = n) (Q : Mem → Prop) (env : Env) :
    SegSound Q env tabs f g x D N := by
  unfold chainSeg? at h
  generalize hfc : freshChain f g 4 (lastArg gv) = r at h
  obtain ⟨ns, m0⟩ := r
  simp only at h
  cases hsf : storesF f (ns.length + 1) x with
  | none => rw [hsf] at h; cases h
  | some r =>
  obtain ⟨fs, z⟩ := r
  rw [hsf] at h
  simp only at h
  cases hzv : f.value? z with
  | none => rw [hzv] at h; cases h
  | some zv =>
  rw [hzv] at h
  simp only at h
  split at h
  case isFalse => cases h
  rename_i hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hfop, hgop⟩, hzop⟩, hzsz⟩, hzm⟩, hzb⟩, hzn⟩, hns⟩, hzip⟩, hst⟩ := hc
  obtain ⟨hsc, hlen⟩ := storesF_chain hsf
  have hfc' := freshChain_chain hfc
  cases fs with
  | nil => cases hlen
  | cons x' fs1 =>
  obtain ⟨hx', fv', hfv', -, hfsz, hsc1⟩ := hsc
  subst x'
  rw [hfv] at hfv'
  cases hfv'
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
  simp only [List.tail_cons]
  refine ⟨?_, ?_⟩
  -- segment roots never panic
  · intro s hs _ sv fr e m hsv hp
    have hop : sv.op = .Store ∨ sv.op = .Zero := by
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with (hs | rfl) | rfl
      · obtain ⟨sv', hsv', hop⟩ := hsc1.store s hs
        rw [hsv] at hsv'; cases hsv'; exact .inl hop
      · rw [hzv] at hsv; cases hsv; exact .inr hzop
      · rw [hfv] at hsv; cases hsv; exact .inl hfop
    rcases Proof.evalValue_panic_op hp with hp | hp <;> rcases hop with hop | hop <;>
      rw [hop] at hp <;> cases hp
  intro S A H hT _ hid hsize hroots
  have hxA : A x := hroots x (by simp) (by simp [CSE.rootNode, hfv, hfop, prio_store])
  have hzA : A z := hroots z (by simp) (by simp [CSE.rootNode, hzv, hzop, prio_zero])
  -- the `Zero`
  have hza := CSE.Mem.args_two hzsz
  rw [hzm] at hza
  have hzcl := H.cl z zv hzA hzv (by rw [hzop]; decide)
  have hpA := hzcl zv.args[0]! (by rw [hza]; simp)
  have hm0A := hzcl m0 (by rw [hza]; simp)
  obtain ⟨_, pv, -, hpv, -⟩ := H.val _ hpA
  obtain ⟨_, mv, -, hmv, -⟩ := H.val _ hm0A
  obtain ⟨zv', yz, hzv', hyz, hevz⟩ := H.val z hzA
  rw [hzv] at hzv'
  cases hzv'
  obtain ⟨P, M0, Z, hPw, rfl, hZ, rfl⟩ := zero_ok hzop hza hpv hmv (hevz (by rw [hzop]; decide))
  have hz : ∀ M, S.regs[z]? = some (some (.mem M)) → M = Z := fun M hM => by
    rw [hyz] at hM
    exact (retype_mem_eq (Option.some.inj (Option.some.inj hM))).2.symm
  -- the anchor
  simp only [List.zip_cons_cons, List.all_cons, hfv, hgv, Bool.and_eq_true] at hzip
  obtain ⟨hss, hzip1⟩ := hzip
  rw [List.filterMap_cons_some hfv, List.reverse_cons] at hst
  obtain ⟨mid, hst1, hst2⟩ := segTiles_append _ _ _ _ hst
  obtain ⟨qv, xv, M1, M2, ha, hA0, hA1, hA2, hq, hqw, hx, hm1, hw, hy, htile⟩ :=
    level_src H hT hid hpA hpv hPw hxA hfv hfop hst2
  obtain ⟨ws1, hz1, ht1, htg⟩ := chain_below H hT hid hpA hpv hPw hm0A hmv hz fs1 ns fv.args[2]!
    (lastArg gv) mid M1 hsc1 hfc' hlen
    (fun n hn => hgid n (by simp [hn])) hzip1 hst1 hm1 hA2
  have hsrc : writes P Z (ws1 ++ [(mid, encode (auxTy tabs fv.aux) xv)]) = some M2 := by
    rw [writes_append, hz1, Option.bind_some, writes_one, hw]
  have htgt := writes_over_zero_eq hZ hsrc (Tiles.append ht1 htile)
  obtain ⟨W1, hW1, hw1⟩ := writes_snoc htgt
  obtain ⟨Fr1, he1, hr1, hag1, hsz1⟩ := htg W1 hW1 S (fun _ _ => rfl) hsize
  unfold segStoreSame at hss
  simp only [Bool.and_eq_true, beq_iff_eq] at hss
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, htop⟩, -⟩, htsz⟩, haux⟩, htype⟩, h0⟩, h1⟩, -⟩, -⟩ := hss
  have hta : gv.args = #[fv.args[0]!, fv.args[1]!, lastArg gv] := by
    rw [lastArg_three htsz, ← h0, ← h1]; exact CSE.Mem.args_three htsz
  have hev := store_eval (env := env) (ctx := Ctx.make tabs g) htop hta
    (by rw [hag1 _ hA0]; exact hq) hqw (by rw [hag1 _ hA1]; exact hx) hr1
    (by rw [show (Ctx.make tabs g).tabs = tabs from rfl, haux]; exact hw1)
  rw [hgid x (by simp) gv hgv, Proof.tys_of_value hgv, Option.getD_some, htype] at hev
  have hxlt : x < Fr1.regs.size := Nat.lt_of_lt_of_le (CheckFacts.lt_of_value? hgv) hsz1
  refine ⟨Fr1.set x ((Val.mem M2).retype (tabs.ty fv.type)), ?_, fun _ => ⟨_, _, hy,
    Proof.Frame.set_regs_self hxlt, Sem.Refines.refl _⟩⟩
  rw [Proof.evalAll_append, he1]
  dsimp only
  rw [Proof.evalAll_cons]
  simp only [Proof.stepV, show (Ctx.make tabs g).f = g from rfl, hgv, hev]
  rfl

/-! ## Non-vacuity: two 8-byte stores over a 16-byte `Zero`

`f`: `v3 = Zero [16] v2 v1`, `v7 = Store {int64} (OffPtr [0] v2) v6 v3`,
`v8 = Store {int64} (OffPtr [8] v2) v6 v7`; `g`: `v8 = Store {int64} v5 v6 v9`, fresh
`v9 = Store {int64} v4 v6 v1`. The segment drops `[v7, v3]` and puts in `[v9]`. -/

section Witness
open GoFV.Proof.CSE.Mem.Witness (tabs val)

private def wv (id : ID) (op : Op) (type : TypeRef) (auxInt : Int64) (aux : Option AuxRef)
    (args : Array ID) : Value :=
  { val id op type aux args with auxInt }

private def wStore (id p m : ID) : Value := wv id .Store 2 0 (some 2) #[p, 6, m]

private def wf : Func :=
  { (default : Func) with
    valueTab := #[none, some (wv 1 .InitMem 2 0 none #[]), some (wv 2 .SP 1 0 none #[]),
      some (wv 3 .Zero 2 16 (some 2) #[2, 1]), some (wv 4 .OffPtr 1 0 none #[2]),
      some (wv 5 .OffPtr 1 8 none #[2]), some (wv 6 .Const64 0 0 none #[]),
      some (wStore 7 4 3), some (wStore 8 5 7)] }

private def wg : Func :=
  { (default : Func) with
    valueTab := #[none, some (wv 1 .InitMem 2 0 none #[]), some (wv 2 .SP 1 0 none #[]),
      none, some (wv 4 .OffPtr 1 0 none #[2]), some (wv 5 .OffPtr 1 8 none #[2]),
      some (wv 6 .Const64 0 0 none #[]), none, some (wStore 8 5 9), some (wStore 9 4 1)] }

theorem chainSeg_witness : chainSeg? tabs wf wg 8 (wStore 8 5 7) (wStore 8 5 9) = some ([7, 3], [9]) := by
  decide +kernel

end Witness

end GoFV.Proof.Seg
