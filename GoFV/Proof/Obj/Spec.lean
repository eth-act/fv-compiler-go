import GoFV.Proof.Obj.Basic

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkObj` accepted (`GoFV/Asm/CheckObj.lean`)

The executable validator's checks as propositions: `sameEffect_spec`, `sameCtl_spec`
(`CtlMatch`), `checkProg_spec`, `checkOne_spec`, `checkBody_spec`, the templates
(`frameOK_spec`, `retOK_spec`, `checkStackCheck_spec`, `checkPrologue_spec`), the offset table
(`startsOf_*`, `offOf_zip`) and `checkObj_spec`.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj

@[simp] private theorem spec_throw {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl

@[simp] private theorem spec_ite_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {b : Except ε α} {v : α} : ((if c then Except.error e else b) = .ok v) ↔ ¬c ∧ b = .ok v := by
  split <;> simp [*]

@[simp] private theorem spec_ite_ok' {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {b : Except ε α} {v : α} : ((if c then b else Except.error e) = .ok v) ↔ c ∧ b = .ok v := by
  split <;> simp [*]

private theorem spec_find_none {p : Nat → Bool} {l : List Nat}
    (h : ∀ c, l.find? p = some c → False) : ∀ r ∈ l, p r = false := by
  have hn : l.find? p = none := Option.eq_none_iff_forall_ne_some.2 h
  intro r hr
  simpa using List.find?_eq_none.1 hn r hr

theorem sameEffect_spec {m p : Sym} (h : sameEffect m p = .ok ()) :
    (∀ r ∈ cmpRegs, m.getX r = p.getX r) ∧ m.getX 30 = .x 30 ∧ p.getX 30 = .x 30 ∧
    m.sp = p.sp ∧ m.fl = p.fl ∧ m.stores = p.stores ∧ (∀ x ∈ m.loads, x ∈ p.loads) ∧
    p.readsTmp = false ∧ (∀ x ∈ p.loads, x ∈ m.loads) := by
  unfold sameEffect at h
  simp only [bind, Except.bind, pure, Except.pure, spec_throw] at h
  split at h
  · cases h
  · rename_i hf
    simp at h
    obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6, h8, h7⟩ := h
    have hn := spec_find_none hf
    exact ⟨fun r hr => by simpa using hn r hr, h1, h2, h3, h4, h5, fun x hx => h6 x.1 x.2 hx, h7,
      fun x hx => h8 x.1 x.2 hx⟩

/-- A branch to Prog `id` reaches offset `q`. -/
def TgtOK (offs : List (Nat × Nat)) (id : Nat) (q : Int) : Prop :=
  ∃ o, offOf offs id = some o ∧ (o : Int) = q

/-- What `sameCtl` accepts. -/
def CtlMatch (offs : List (Nat × Nat)) (_pr : Sym) : MCtl → PCtl → Prop
  | .fall, .fall => True
  | .jmp q, .jmp id => TgtOK offs id q
  | .cond fl c q, .cond c' id => fl = .init ∧ c = c' ∧ TgtOK offs id q
  | .cbz sf nz a q, .cbz sf' nz' a' id =>
    sf = sf' ∧ nz = nz' ∧ a = a' ∧ a'.regsOK = true ∧ TgtOK offs id q
  | .tbz nz b a q, .tbz nz' b' a' id =>
    nz = nz' ∧ b = b' ∧ a = a' ∧ a'.regsOK = true ∧ TgtOK offs id q
  | .call n add, .call n' add' => n = n' ∧ add = add' ∧ add = 0
  | .callReg a, .callReg a' => a = a' ∧ a'.regsOK = true
  | _, _ => False

theorem sameCtl_spec {offs : List (Nat × Nat)} {m : MCtl} {p : PCtl} {pr : Sym}
    (h : sameCtl offs m p pr = .ok ()) : CtlMatch offs pr m p := by
  unfold sameCtl at h
  cases m <;> cases p <;> simp [pure, Except.pure] at h <;> simp only [CtlMatch, TgtOK]
  case jmp.jmp =>
    split at h
    · rename_i o ho
      simp at h
      exact ⟨o, ho, h⟩
    · cases h
  case cond.cond =>
    obtain ⟨h1, h2, h⟩ := h
    refine ⟨h1, h2, ?_⟩
    split at h
    · rename_i o ho
      simp at h
      exact ⟨o, ho, h⟩
    · cases h
  case cbz.cbz =>
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h⟩ := h
    refine ⟨h1, h2, h3, h4, ?_⟩
    split at h
    · rename_i o ho
      simp at h
      exact ⟨o, ho, h⟩
    · cases h
  case tbz.tbz =>
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h⟩ := h
    refine ⟨h1, h2, h3, h4, ?_⟩
    split at h
    · rename_i o ho
      simp at h
      exact ⟨o, ho, h⟩
    · cases h
  case call.call =>
    exact ⟨h.1.1, h.1.2, h.2⟩
  case callReg.callReg =>
    exact ⟨h.1, h.2⟩

theorem checkProg_spec {t : ByteArray} {rs : List Reloc} {offs : List (Nat × Nat)} {az ez : Int}
    {p : Prog} {o e : Nat} (h : checkProg t rs offs az ez p o e = .ok ()) :
    ((p.isSkip = true ∨ p.as = .END) ∧ o = e) ∨
    (p.isSkip = false ∧ p.as ≠ .END ∧ o < e ∧ (e - o) % 4 = 0 ∧ ∃ pσ pc mσ mc,
      progSym az ez p = .ok (pσ, pc) ∧ symWords t rs ((e - o) / 4) o {} = .ok (mσ, mc) ∧
      sameEffect mσ pσ = .ok () ∧ sameCtl offs mc pc pσ = .ok ()) := by
  unfold checkProg at h
  simp [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hc
    simp at h
    exact Or.inl ⟨hc, h⟩
  · rename_i hc
    simp at h hc
    obtain ⟨hw, h⟩ := h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · cases h
      · rename_i w hw'
        split at h
        · cases h
        · rename_i u hu
          exact Or.inr ⟨hc.1, hc.2, by omega, by omega, v.1, v.2, w.1, w.2, hv, hw', hu, h⟩

/-- A P0 `RET` (without operand, or of a symbol: a tail call). -/
def isRet0 (p : Prog) : Bool := p.as == .RET && (p.to.type == .NONE || p.to.sym.isSome)

/-- Where a P0 `RET`'s epilogue goes. -/
def retBack (az : Int) (leaf : Bool) (p : Prog) : MCtl :=
  match p.to.sym with
  | some y => MCtl.jmpSym y p.to.offset
  | none => .reg (if az == 0 || leaf then .x 30 else .ld 8 .sp)

theorem checkOne_spec {t : ByteArray} {rs : List Reloc} {offs : List (Nat × Nat)} {az ez : Int}
    {leaf : Bool} {p : Prog} {s e : Nat} (h : checkOne t rs offs az ez leaf p s e = .ok ()) :
    (isRet0 p = true ∧ s < e ∧ (e - s) % 4 = 0 ∧ ∃ σ c,
      symWords t rs ((e - s) / 4) s {} = .ok (σ, c) ∧ retOK az leaf σ c (retBack az leaf p) = .ok ()) ∨
    (isRet0 p = false ∧ checkProg t rs offs az ez p s e = .ok ()) := by
  unfold checkOne at h
  split at h
  · rename_i hc
    left
    split at h
    · cases h
    · rename_i hw
      simp at hw
      refine ⟨hc, by omega, by omega, ?_⟩
      split at h
      · cases h
      · rename_i σ c hs
        refine ⟨σ, c, hs, ?_⟩
        dsimp only at h
        split at h
        · rename_i hr
          exact hr
        · cases h
  · rename_i hc
    right
    refine ⟨by simpa [isRet0] using hc, ?_⟩
    split at h
    · rename_i hr
      exact hr
    · cases h

theorem checkBody_spec {t : ByteArray} {rs : List Reloc} {offs : List (Nat × Nat)} {az ez : Int}
    {leaf : Bool} : ∀ (ps : List Prog) (ss : List Nat) (lastEnd : Nat),
    checkBody t rs offs az ez leaf ps ss lastEnd = .ok () → ∀ (hlen : ss.length = ps.length),
    ∀ k (hk : k < ps.length),
      checkOne t rs offs az ez leaf ps[k] (ss[k]'(by omega)) (ss.getD (k + 1) lastEnd) = .ok () := by
  intro ps
  induction ps with
  | nil => intro ss lastEnd _ _ k hk; simp at hk
  | cons p ps ih =>
    intro ss lastEnd h hlen k hk
    cases ss with
    | nil => simp at hlen
    | cons s ss =>
      simp only [checkBody, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i u hone
        cases k with
        | zero =>
          cases ss <;> exact hone
        | succ k =>
          exact ih ss lastEnd h (by simpa using hlen) k (by simpa using hk)

theorem startsOf_length (e : Nat) (os : List (Option Nat)) : (startsOf e os).length = os.length := by
  induction os with
  | nil => rfl
  | cons o os ih => simp [startsOf, ih]

theorem startsOf_getElem (e : Nat) (os : List (Option Nat)) (k : Nat)
    (hk : k < (startsOf e os).length) :
    (startsOf e os)[k] = (os[k]'(by rw [startsOf_length] at hk; exact hk)).getD
      ((startsOf e os).getD (k + 1) e) := by
  induction os generalizing k with
  | nil => simp [startsOf] at hk
  | cons o os ih =>
    cases k with
    | zero =>
      simp only [startsOf, List.getElem_cons_zero, List.getD_cons_succ]
      cases startsOf e os <;> rfl
    | succ k =>
      simp only [startsOf, List.getElem_cons_succ, List.getD_cons_succ]
      exact ih k _

/-- A lookup in the ID ↦ offset table finds the offset of a Prog with that ID. -/
theorem offOf_zip {ps : List Prog} {ss : List Nat} {id q : Nat} (hlen : ss.length = ps.length)
    (h : offOf ((ps.zip ss).map fun (p, s) => (p.id, s)) id = some q) :
    ∃ k, ∃ hk : k < ps.length, ps[k].id = id ∧ ss[k]'(by omega) = q := by
  induction ps generalizing ss with
  | nil => simp [offOf] at h
  | cons p ps ih =>
    cases ss with
    | nil => simp at hlen
    | cons s ss =>
      simp only [List.zip_cons_cons, List.map_cons, offOf, List.lookup] at h
      split at h
      · rename_i heq
        simp at heq h
        exact ⟨0, by simp, heq.symm, h⟩
      · obtain ⟨k, hk, h1, h2⟩ := ih (by simpa using hlen) h
        exact ⟨k + 1, by simp; omega, by simpa using h1, by simpa using h2⟩

/-- The frame's prologue store pair. -/
def frameStores (az : Int) : List (Ex × Nat × Ex) :=
  [(Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az))), 8, Ex.x 30),
   (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8))), 8, Ex.x 29)]

theorem frameOK_spec {az : Int} {σ : Sym} (h : frameOK az σ = .ok ()) :
    σ.sp = Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az))) ∧
    σ.getX 29 = Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8))) ∧
    (∀ r ∈ cmpRegs, r ≠ 29 → r ≠ 20 → σ.getX r = .x r) ∧ σ.getX 30 = .x 30 ∧
    (σ.stores = frameStores az ∨ σ.stores = (frameStores az).reverse) ∧ σ.loads = [] := by
  unfold frameOK at h
  simp [bind, Except.bind, pure, Except.pure] at h
  obtain ⟨h1, h2, h⟩ := h
  split at h
  · cases h
  · rename_i hf
    have hn := spec_find_none hf
    simp at h
    obtain ⟨h3, h4, h5⟩ := h
    refine ⟨h1, h2, fun r hr h29 h20 => by simpa [h29, h20] using hn r hr, h3, ?_, h5⟩
    simp only [frameStores, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    by_cases e : σ.stores = [(Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az))), 8, Ex.x 30),
      (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8))), 8, Ex.x 29)]
    · exact Or.inl e
    · exact Or.inr (h4 e)

theorem retOK_spec {az : Int} {leaf : Bool} {σ : Sym} {c back : MCtl}
    (h : retOK az leaf σ c back = .ok ()) :
    (az = 0 ∧ σ = {} ∧ c = back) ∨
    (az ≠ 0 ∧ σ.sp = Ex.mkAdd .sp (.k (BitVec.ofInt 64 az)) ∧
      σ.getX 29 = (if leaf then Ex.mkAdd .sp (.k (BitVec.ofInt 64 (az - 8)))
        else .ld 8 (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-8))))) ∧
      σ.getX 30 = (if leaf then Ex.x 30 else .ld 8 .sp) ∧
      (∀ r ∈ cmpRegs, r ≠ 29 → σ.getX r = .x r) ∧ σ.fl = .init ∧ σ.stores = [] ∧ c = back ∧
      ∀ x ∈ σ.loads, x = (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-8))), 8) ∨ x = (Ex.sp, 8)) := by
  unfold retOK at h
  simp [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i haz
    simp at h
    exact Or.inl ⟨haz, h⟩
  · rename_i haz
    simp at h
    obtain ⟨h1, h2, h3, h⟩ := h
    split at h
    · cases h
    · rename_i hf
      have hn := spec_find_none hf
      simp at h
      refine Or.inr ⟨haz, h1, ?_, h3, fun r hr h29 => by simpa [h29] using hn r hr, h.1, h.2.1,
        h.2.2.2, fun ⟨a, b⟩ hx => ?_⟩
      · rw [h2]
        simp
      · rcases h.2.2.1 a b hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (by simp)
        · exact Or.inr rfl

theorem checkStackCheck_spec {t : ByteArray} {rs : List Reloc} {az : Int} {o gOff ce tail : Nat}
    (h : checkStackCheck t rs az o gOff = .ok (ce, tail)) :
    az ≤ 4096 ∧ ∃ σ,
      symWords t rs (if az ≤ 128 then 3 else 4) o {} =
        .ok (σ, .cond (.addSub true true
          (if az ≤ 128 then Ex.sp else Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-(az - 128)))))
          (.ld 8 (Ex.mkAdd (.x 28) (.k (BitVec.ofNat 64 gOff))))) 9 (tail : Int)) ∧
      ce = o + 4 * (if az ≤ 128 then 3 else 4) ∧ σ.stores = [] ∧ σ.sp = .sp ∧ σ.getX 30 = .x 30 ∧
      σ.loads = [(Ex.mkAdd (.x 28) (.k (BitVec.ofNat 64 gOff)), 8)] ∧
      (∀ r ∈ cmpRegs, r ≠ 16 → r ≠ 17 → σ.getX r = .x r) := by
  unfold checkStackCheck at h
  simp [bind, Except.bind, pure, Except.pure] at h
  obtain ⟨haz, h⟩ := h
  refine ⟨haz, ?_⟩
  split at h
  · cases h
  · rename_i v hv
    obtain ⟨σ, c⟩ := v
    dsimp only at h
    split at h
    · rename_i fl q
      simp at h
      obtain ⟨hfl, hst, hsp, hx30, hld, h⟩ := h
      split at h
      · cases h
      · rename_i hf
        have hn := spec_find_none hf
        simp at h
        obtain ⟨hq, hce, htl⟩ := h
        subst hfl
        refine ⟨σ, ?_, hce.symm, hst, hsp, hx30, hld,
          fun r hr h16 h17 => by simpa [h16, h17] using hn r hr⟩
        rw [hv, ← htl, Int.toNat_of_nonneg (by omega)]
        rfl
    · cases h

theorem checkPrologue_spec {t : ByteArray} {rs : List Reloc} {az : Int} {body : Nat}
    {check : Option (Nat × Nat × Nat)} (h : checkPrologue t rs az body = .ok check) :
    (az = 0 ∧ body = 0 ∧ check = none) ∨
    (az ≠ 0 ∧ ∃ fo σ,
      ((check = none ∧ fo = 0) ∨ ∃ ce tail gOff, check = some (ce, tail, gOff) ∧ fo = ce ∧
        (gOff = 16 ∨ gOff = 24) ∧ checkStackCheck t rs az 0 gOff = .ok (ce, tail)) ∧
      fo < body ∧ (body - fo) % 4 = 0 ∧ symWords t rs ((body - fo) / 4) fo {} = .ok (σ, .fall) ∧
      frameOK az σ = .ok ()) := by
  unfold checkPrologue at h
  simp [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i haz
    simp at h
    exact Or.inl ⟨haz, h.1, h.2.symm⟩
  · rename_i haz
    right
    refine ⟨haz, ?_⟩
    split at h
    · rename_i gOff hg
      have hg' : gOff = 16 ∨ gOff = 24 := by
        split at hg <;> (try split at hg) <;> simp at hg <;> omega
      cases hc : checkStackCheck t rs az 0 gOff with
      | error e => simp [hc] at h
      | ok r =>
        obtain ⟨ce, tail⟩ := r
        simp [hc] at h
        obtain ⟨hw, h⟩ := h
        split at h
        · cases h
        · rename_i v hv
          simp at h
          obtain ⟨hf, h⟩ := h
          split at h
          · cases h
          · rename_i u hu
            simp at h
            refine ⟨ce, v.1, Or.inr ⟨ce, tail, gOff, h.symm, rfl, hg', hc⟩, by omega, by omega,
              ?_, hu⟩
            rw [hv, ← hf]
    · rename_i hg
      simp at h
      obtain ⟨hw, h⟩ := h
      split at h
      · cases h
      · rename_i v hv
        simp at h
        obtain ⟨hf, h⟩ := h
        split at h
        · cases h
        · rename_i u hu
          simp at h
          refine ⟨0, v.1, Or.inl ⟨h.symm, rfl⟩, by omega, by simpa using hw.2, ?_, hu⟩
          simp only [Nat.sub_zero]
          rw [hv, ← hf]

private theorem spec_forIn'_head {l : List Nat} {acc v : Array (Option Nat)}
    {f : (a : Nat) → a ∈ l → Array (Option Nat) → Except String (ForInStep (Array (Option Nat)))}
    (hf : ∀ a h acc s, f a h acc = .ok s → ∃ x, s = .yield (acc.push x))
    (h0 : acc[0]? = some none) (h : forIn' l acc f = .ok v) : v[0]? = some none := by
  induction l generalizing acc with
  | nil =>
    cases h
    exact h0
  | cons a l ih =>
    rw [List.forIn'_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i s hs
      obtain ⟨x, rfl⟩ := hf _ _ _ _ hs
      refine ih (fun a h acc s hs => hf a _ acc s hs) ?_ h
      have : 0 < acc.size := by
        rcases Nat.eq_zero_or_pos acc.size with e | e
        · simp [e] at h0
        · exact e
      rw [Array.getElem?_push_lt this, ← h0, Array.getElem?_eq_getElem this]

private theorem spec_bne {a b c d : Nat} (h : ¬((a != b || c != d) = true)) : a = b ∧ c = d := by
  simpa using h

private theorem spec_starts {L n body : Nat} {v : Array (Option Nat)} (hv0 : v[0]? = some none)
    (hlen : (startsOf L v.toList).length = n) (hn : 2 ≤ n)
    (hhd : (startsOf L v.toList).headD 0 = body) :
    (startsOf L v.toList).toArray.size = n ∧ (startsOf L v.toList).toArray[0]? = some body ∧
      (startsOf L v.toList).toArray[1]? = some body := by
  obtain ⟨l⟩ := v
  cases l with
  | nil => simp at hv0
  | cons x rest =>
    simp at hv0
    subst hv0
    simp only [startsOf] at hlen hhd ⊢
    cases hr : startsOf L rest with
    | nil =>
      rw [hr] at hlen
      simp at hlen
      omega
    | cons y ys =>
      rw [hr] at hlen hhd
      simp at hlen hhd ⊢
      omega

private theorem spec_all {ps : Array Prog}
    (h : ((ps.toList.map (·.id)).all fun x => decide (x < 2 ^ 32)) = true) :
    ∀ p ∈ ps.toList, p.id < 2 ^ 32 := by
  intro p hp
  simpa using List.all_eq_true.1 h p.id (List.mem_map_of_mem hp)

theorem checkObj_spec {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    (h : checkObj ps spills o = .ok tab) :
    ∃ text body, ps[0]? = some text ∧ text.as = .TEXT ∧ (ps.toList.map (·.id)).Nodup ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ 2 ≤ ps.size ∧ tab.offs.size = ps.size ∧
      tab.offs[0]? = some body ∧ tab.offs[1]? = some body ∧ tab.leaf = leafOf ps ∧
      checkPrologue o.text o.relocs.toList tab.autosize body = .ok tab.check ∧
      (∀ ce tail gOff, tab.check = some (ce, tail, gOff) → tab.endOff = tail) ∧
      checkBody o.text o.relocs.toList ((ps.toList.zip tab.offs.toList).map fun (p, s) => (p.id, s))
        tab.autosize tab.extrasize tab.leaf (ps.toList.drop 1) (tab.offs.toList.drop 1)
        tab.endOff = .ok () := by
  unfold checkObj at h
  cases h0 : ps[0]? with
  | none =>
    rw [h0] at h
    cases h
  | some text =>
    rw [h0] at h
    simp only [bind, Except.bind, pure, Except.pure, spec_throw, spec_ite_ok, spec_ite_ok'] at h
    obtain ⟨hT, hND, hall, hsz, h⟩ := h
    split at h
    case h_2 => cases h
    · rename_i t2 _
      split at h
      · cases h
      · rename_i v hv
        have hv0 : v[0]? = some none := by
          rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at hv
          refine spec_forIn'_head ?_ rfl hv
          intro a ha acc s hs
          split at hs
          · split at hs
            · cases hs
            · cases hs
              exact ⟨_, rfl⟩
          · split at hs
            · cases hs
              exact ⟨_, rfl⟩
            · cases hs
        split at h
        · cases h
        · rename_i chk hchk
          rw [spec_ite_ok] at h
          obtain ⟨hpc, h⟩ := h
          obtain ⟨hlen, hhd⟩ := spec_bne hpc
          obtain ⟨e1, e2, e3⟩ := spec_starts hv0 hlen (by omega) hhd
          split at h
          · cases h
          · rename_i u hbody
            split at h
            · split at h
              · cases h
              · cases h
                refine ⟨text, _, rfl, by simpa using hT, hND, spec_all hall, by omega, e1, e2,
                  e3, rfl, hchk, ?_, hbody⟩
                intro ce tail gOff hc
                simp at hc
                obtain ⟨rfl, rfl, rfl⟩ := hc
                rfl
            · cases h
              refine ⟨text, _, rfl, by simpa using hT, hND, spec_all hall, by omega, e1, e2,
                e3, rfl, hchk, ?_, hbody⟩
              intro ce' tail' gOff' hc
              first
              | (rename_i hnm; exact (hnm _ _ _ hc).elim)
              | cases hc

end GoFV.Proof.Obj
