import GoFV.Proof.Pass.LoadFwdArg
import GoFV.Proof.Pass.DSEMem
import GoFV.Proof.NilPre
import GoFV.Proof.Pass.ECChain
import GoFV.Proof.Pass.ECTree

/-!
# Dropped identity writes (issues #151, #69)

The forwarding layer turns a memory root whose write changes no byte into a `Copy` of its memory
(`RewriteCheck.dropOK`): a `Store` of a zero-sized type (`generic.rules:1005`), a `Store` of a
term of a zero value (`ZeroV`: `0`, `false`, `poison`, the empty value or a composite of such;
`zeroConst`: a constant term such as `Const64 [0]`, `ConstNil`, `ConstString {""}`, or a selection
of a zero component such as `SliceLen (SliceMake p (Const64 [0]) c)`; `zeroAt_den`) into zero
bytes (`:943`, `:948`, `:954`, `:961`, `:1357`, `:1362`), a
`Zero` of a `Zero` of the same size at an equal pointer (`:2158`), a `Zero` of zero bytes
(`:1352`). `drop_mem`: the dropped root's memory is refined by its memory argument's, as every
byte written refines the byte already there (`write_refines_self`): the encoding of a zero
value has `0` or `poison` bytes (`encode_zero`), and the bytes a successful write
overwrites read back as zeros through the disjoint writes of the chain (`zeroChain_read`) from a
`Zero` that cleared them or from the memory of a malloc call that returned a fresh zeroed block
(`fresh_blockZero`, under the frame invariant `FreshQ` the forwarding layer's source invariant
keeps with `Env.AllocZero`); a zero-sized write is the identity.
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.CSE.Mem GoFV.Proof.Pass.Rewrite

/-! ## Writes of the bytes already there -/

/-- **Writing back the bytes a read gave** changes nothing. -/
theorem write_read_id {m m' : Mem} {p : Ptr} {bs : Array Byte} (hr : m.read p bs.size = some bs)
    (hw : m.write p bs = some m') : m' = m := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw; cases hw; rfl
  simp only [he, Bool.false_eq_true, ite_false] at hw
  have hsz : bs.size ≠ 0 := by simpa [Array.isEmpty_iff_size_eq_zero] using he
  obtain ⟨a, ha, h1, -, -, hbs⟩ := read_some hsz hr
  rw [ha] at hw
  simp only [Option.bind_eq_bind, Option.bind_some] at hw
  split at hw
  · cases hw
    have hdata : (List.range bs.size).foldl (fun d i => d.set! (p.off.toNat + i) bs[i]!) a.data =
        a.data := by
      apply Array.ext_getElem?
      intro j
      by_cases hj : p.off.toNat ≤ j ∧ j < p.off.toNat + bs.size
      · obtain ⟨i, rfl⟩ : ∃ i, j = p.off.toNat + i := ⟨j - p.off.toNat, by omega⟩
        have hi : i < bs.size := by omega
        rw [foldl_set_put p.off.toNat bs i (List.range bs.size) a.data List.nodup_range
          (List.mem_range.2 hi) (by omega), getElem!_pos bs i hi, ← Array.getElem?_eq_getElem hi]
        conv => lhs; rw [hbs]
        rw [Array.getElem?_extract_of_lt (by omega), Array.getElem?_eq_getElem (by omega)]
      · exact foldl_set_get p.off.toNat bs j _ _ fun i hi he => hj ⟨by omega, by
          have := List.mem_range.1 hi; omega⟩
    rw [hdata]
    exact GoFV.Proof.DSE.set_self ha
  · cases hw

/-- **A write of bytes refining those already there** (in a refinement `m'` of the written
memory `m`) gives a memory `m'` refines. -/
theorem write_refines_self {m m' m1 : Mem} (h : Mem.Refines m m') {p : Ptr} {bs bs0 : Array Byte}
    (hr : m'.read p bs.size = some bs0) (hw : m.write p bs = some m1) (hb : BytesRefineA bs bs0) :
    Mem.Refines m1 m' := by
  obtain ⟨m1', hw', hR⟩ := h.write hb hw
  rw [hb.size_eq] at hr
  rw [write_read_id hr hw'] at hR
  exact hR

/-- Bytes that are `0` or `poison` are refined by zeros. -/
theorem zeros_refine : ∀ {l : List Byte}, (∀ c ∈ l, c = .b 0 ∨ c = .poison) →
    BytesRefine l (List.replicate l.length (.b 0))
  | [], _ => .nil
  | c :: l, h => by
    refine .cons ?_ (zeros_refine fun c hc => h c (List.mem_cons_of_mem _ hc))
    rcases h c List.mem_cons_self with rfl | rfl
    · exact .refl _
    · exact .poison _

/-! ## Zero values -/

/-- A `0`, `false`, `poison`, the empty value, or a composite of such (`zeroVal`). -/
inductive ZeroV : Val → Prop
  | poison : ZeroV .poison
  | bool : ZeroV (.bool false)
  | int (w : Width) : ZeroV (.int w 0)
  | empty : ZeroV .empty
  | agg {vs : List Val} : (∀ v ∈ vs, ZeroV v) → ZeroV (.agg vs)

theorem intBytes_zero (n : Nat) : ∀ c ∈ (intBytes n 0).toList, c = .b 0 ∨ c = .poison := by
  intro c hc
  simp only [intBytes, Nat.zero_div, Array.toList_map, List.mem_map] at hc
  obtain ⟨_, -, rfl⟩ := hc
  exact .inl rfl

theorem replicate_poison_zero (n : Nat) :
    ∀ c ∈ (Array.replicate n Byte.poison).toList, c = .b 0 ∨ c = .poison := by
  intro c hc
  simp only [Array.toList_replicate, List.mem_replicate] at hc
  exact .inr hc.2

private theorem putBytes_loop_zero {src : Array Byte}
    (hs : ∀ c ∈ src.toList, c = .b 0 ∨ c = .poison) (off : Nat) :
    ∀ (l : List Nat) (d : Array Byte), (∀ c ∈ d.toList, c = .b 0 ∨ c = .poison) →
      ∀ c ∈ (l.foldl (fun d i => if off + i < d.size then d.set! (off + i) src[i]! else d)
        d).toList, c = .b 0 ∨ c = .poison
  | [], _, h => h
  | i :: l, d, h => by
    refine putBytes_loop_zero hs off l _ ?_
    dsimp only
    split
    · intro c hc
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds] at hc
      rcases List.mem_or_eq_of_mem_set hc with h' | rfl
      · exact h _ h'
      · by_cases hi : i < src.size
        · rw [getElem!_pos src i hi]; exact hs _ (Array.getElem_mem_toList hi)
        · rw [getElem!_neg src i hi]; exact .inl rfl
    · exact h

/-- Writing bytes that are `0` or `poison` into such bytes leaves such bytes. -/
theorem putBytes_zero {src : Array Byte} (hs : ∀ c ∈ src.toList, c = .b 0 ∨ c = .poison)
    (off : Nat) (d : Array Byte) (hd : ∀ c ∈ d.toList, c = .b 0 ∨ c = .poison) :
    ∀ c ∈ (putBytes d off src).toList, c = .b 0 ∨ c = .poison :=
  putBytes_loop_zero hs off _ d hd

theorem encodeWord_zero {v : Val} (h : ZeroV v) :
    ∀ c ∈ (encodeWord v).toList, c = .b 0 ∨ c = .poison := by
  cases h with
  | int w =>
    cases w with
    | w64 => simpa [encodeWord] using intBytes_zero 8
    | _ => simp only [encodeWord]; exact replicate_poison_zero _
  | _ => simp only [encodeWord]; exact replicate_poison_zero _

theorem encodeWords_zero : ∀ {vs : List Val}, (∀ v ∈ vs, ZeroV v) → ∀ (os : List Nat)
    (buf : Array Byte), (∀ c ∈ buf.toList, c = .b 0 ∨ c = .poison) →
      ∀ c ∈ (encodeWords buf os vs).toList, c = .b 0 ∨ c = .poison
  | [], _, os, buf, hb => by cases os <;> simpa [encodeWords] using hb
  | v :: vs, hz, [], buf, hb => by simpa [encodeWords] using hb
  | v :: vs, hz, o :: os, buf, hb => by
    simp only [encodeWords]
    exact encodeWords_zero (fun w hw => hz w (List.mem_cons_of_mem _ hw)) os _
      (putBytes_zero (encodeWord_zero (hz v List.mem_cons_self)) o _ hb)

theorem encodeFields_zero : ∀ {vs : List Val},
    (∀ v ∈ vs, ∀ t, ∀ c ∈ (encode t v).toList, c = .b 0 ∨ c = .poison) →
    ∀ (fs : List (Nat × Ty)) (buf : Array Byte), (∀ c ∈ buf.toList, c = .b 0 ∨ c = .poison) →
      ∀ c ∈ (encodeFields buf fs vs).toList, c = .b 0 ∨ c = .poison
  | [], _, fs, buf, hb => by cases fs <;> simpa [encodeFields] using hb
  | v :: vs, hz, [], buf, hb => by simpa [encodeFields] using hb
  | v :: vs, hz, (o, t) :: fs, buf, hb => by
    simp only [encodeFields]
    exact encodeFields_zero (fun w hw => hz w (List.mem_cons_of_mem _ hw)) fs _
      (putBytes_zero (hz v List.mem_cons_self t) o _ hb)

/-- **The bytes of a zero value**, at every shape, are `0` or `poison`. -/
theorem encode_zero {v : Val} (h : ZeroV v) (t : Ty) :
    ∀ c ∈ (encode t v).toList, c = .b 0 ∨ c = .poison := by
  induction h generalizing t with
  | poison => rw [encode_poison]; exact replicate_poison_zero _
  | bool =>
    cases t with
    | bool => intro c hc; simp [encode] at hc; exact .inl hc
    | _ => simp only [encode]; exact replicate_poison_zero _
  | int w =>
    cases t with
    | int w' =>
      simp only [encode]
      split
      · simpa using intBytes_zero w'.bytes
      · exact replicate_poison_zero _
    | ptr e =>
      cases w with
      | w64 => simpa [encode] using intBytes_zero 8
      | _ => simp only [encode]; exact replicate_poison_zero _
    | _ => simp only [encode]; exact replicate_poison_zero _
  | empty => cases t <;> (simp only [encode]; exact replicate_poison_zero _)
  | agg hz ih =>
    cases t with
    | agg fs n => simp only [encode]; exact encodeFields_zero ih fs _ (replicate_poison_zero _)
    | str => simp only [encode]; exact encodeWords_zero hz _ _ (replicate_poison_zero _)
    | slice e => simp only [encode]; exact encodeWords_zero hz _ _ (replicate_poison_zero _)
    | _ => simp only [encode]; exact replicate_poison_zero _

/-! ## The dropped roots -/

/-- `Val.retype` fixes `mem` only at the memory shape. -/
theorem retype_mem {t : Ty} {M M' : Mem} (h : (Val.mem M').retype t = .mem M) : M' = M := by
  cases t <;> simp [Val.retype] at h
  exact h

/-- Only a memory retypes to a memory. -/
theorem retype_eq_mem {t : Ty} {v : Val} {M : Mem} (h : v.retype t = .mem M) : v = .mem M := by
  unfold Val.retype at h
  split at h <;> (repeat' split at h) <;>
    (try simp only [Val.ofStr, Val.ofSlice] at h) <;> (try split at h) <;> simp_all

/-- A `Store`'s write: a pointer word, a memory and the written memory. -/
theorem memDef_store {tabs : Tables} {s : Value} (hs : s.op = .Store ∨ s.op = .StoreWB)
    {a b c y : Val} (h : memDef tabs s [a, b, c] = some y) :
    ∃ q m0 M', a.asPtrWord = some q ∧ c = .mem m0 ∧
      m0.write q (encode (auxTy tabs s.aux) b) = some M' ∧ y = .mem M' := by
  rcases hs with hs | hs <;>
  · cases c <;> try (simp [memDef, hs] at h; done)
    rename_i m0
    simp only [memDef, hs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, M', hw, rfl⟩ := h
    exact ⟨q, m0, M', hq, rfl, hw, rfl⟩

/-- A `Zero`'s write: a pointer word, a memory and the written memory. -/
theorem memDef_zero {tabs : Tables} {s : Value} (hs : s.op = .Zero) {a c y : Val}
    (h : memDef tabs s [a, c] = some y) :
    ∃ q m0 M', a.asPtrWord = some q ∧ c = .mem m0 ∧
      m0.write q (Array.replicate s.auxInt.toInt.toNat (.b 0)) = some M' ∧ y = .mem M' := by
  cases c <;> try (simp [memDef, hs] at h; done)
  rename_i m0
  simp only [memDef, hs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, M', hw, rfl⟩ := h
  exact ⟨q, m0, M', hq, rfl, hw, rfl⟩

mutual
theorem zeroVal_spec : ∀ {v : Val}, zeroVal v = true → ZeroV v
  | .poison, _ => .poison
  | .bool false, _ => .bool
  | .bool true, h => by simp [zeroVal] at h
  | .empty, _ => .empty
  | .int w c, h => by
    simp only [zeroVal, beq_iff_eq] at h
    subst h; exact .int w
  | .agg vs, h => .agg (zeroVals_spec (by simpa [zeroVal] using h))
  | .mem _, h | .tuple _, h | .ptr _, h | .blob _, h => by simp [zeroVal] at h
theorem zeroVals_spec : ∀ {vs : List Val}, zeroVals vs = true → ∀ v ∈ vs, ZeroV v
  | [], _, _, hv => absurd hv List.not_mem_nil
  | v :: vs, h, _, .head _ => by
    simp only [zeroVals, Bool.and_eq_true] at h
    exact zeroVal_spec h.1
  | v :: vs, h, w, .tail _ hw => by
    simp only [zeroVals, Bool.and_eq_true] at h
    exact zeroVals_spec h.2 w hw
end

private theorem refinesList_mem : ∀ {as bs : List Val}, Sem.RefinesList as bs →
    ∀ a ∈ as, ∃ b ∈ bs, Sem.Refines a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hr hl, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, h'⟩ := refinesList_mem hl a h
      exact ⟨b, List.mem_cons_of_mem _ hb, h'⟩

/-- A value refined by a zero value is one. -/
theorem zeroV_of_refines {a b : Val} (h : Sem.Refines a b) (hb : ZeroV b) : ZeroV a := by
  induction hb generalizing a with
  | poison => cases h; exact .poison
  | bool => cases h <;> constructor
  | int w => cases h <;> constructor
  | empty => cases h <;> constructor
  | agg _ ih =>
    cases h with
    | poison => exact .poison
    | agg hl =>
      exact .agg fun a' ha' => by
        obtain ⟨b', hb', hr⟩ := refinesList_mem hl a' ha'
        exact ih b' hb' hr

theorem valPath_poison : ∀ ps : List Nat, valPath ps .poison = .poison
  | [] => rfl
  | _ :: _ => rfl

/-- A value refined by one whose component `ps` is zero has a zero component `ps`. -/
theorem zeroV_path_of_refines : ∀ (ps : List Nat) {a b : Val}, Sem.Refines a b →
    ZeroV (valPath ps b) → ZeroV (valPath ps a)
  | [], _, _, h, hb => zeroV_of_refines h hb
  | i :: ps, _, _, h, hb => by
    cases h with
    | poison => rw [valPath_poison]; exact .poison
    | agg hl =>
      simp only [valPath] at hb ⊢
      exact zeroV_path_of_refines ps (GoFV.Proof.EC.ec_getD_mono hl i) hb
    | _ => simp only [valPath]; exact .poison

/-- A composite retypes to `poison` or a composite. -/
theorem retype_agg_cases (vs : List Val) (t : Ty) :
    (Val.agg vs).retype t = .poison ∨ ∃ vs', (Val.agg vs).retype t = .agg vs' := by
  cases t with
  | agg fs n =>
    simp only [Val.retype]
    split
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl
  | str =>
    match vs with
    | [p, l] =>
      simp only [Val.retype, Val.ofStr]
      split
      · exact .inr ⟨_, rfl⟩
      · exact .inl rfl
    | [] | [_] | _ :: _ :: _ :: _ => exact .inl rfl
  | slice e =>
    match vs with
    | [p, l, c] =>
      simp only [Val.retype, Val.ofSlice]
      split
      · exact .inr ⟨_, rfl⟩
      · exact .inl rfl
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => exact .inl rfl
  | _ => exact .inl rfl

/-- **A retyped zero value is one.** -/
theorem zeroV_retype {v : Val} (h : ZeroV v) (t : Ty) : ZeroV (v.retype t) := by
  induction h generalizing t with
  | poison => rw [Rewrite.retype_poison]; exact .poison
  | bool => cases t <;> simp only [Val.retype] <;> constructor
  | int w =>
    cases t with
    | int w' =>
      simp only [Val.retype]
      split
      · rw [show BitVec.setWidth w'.bits (0 : BitVec w.bits) = 0 by simp]; exact .int _
      · exact .poison
    | ptr e =>
      cases w with
      | w64 => exact .int _
      | _ => exact .poison
    | _ => exact .poison
  | empty => cases t <;> simp only [Val.retype] <;> constructor
  | @agg vs _ ih =>
    rcases retype_agg_cases vs t with hr | ⟨vs', hr⟩
    · rw [hr]; exact .poison
    · obtain ⟨_, he, hc⟩ := retype_eq_agg hr
      cases he
      rw [hr]
      refine .agg fun v' hv' => ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv'
      obtain ⟨t', ht'⟩ := hc i
      rw [show vs'[i] = vs'.getD i .poison by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some], ht']
      by_cases hi' : i < vs.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
        exact ih _ (List.getElem_mem hi') t'
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
          Rewrite.retype_poison]
        exact .poison

/-- **A retyped value with a zero component `ps` has one.** -/
theorem zeroV_path_retype : ∀ (ps : List Nat) {v : Val} (t : Ty), ZeroV (valPath ps v) →
    ZeroV (valPath ps (v.retype t))
  | [], _, t, h => zeroV_retype h t
  | i :: ps, v, t, h => by
    cases hr : v.retype t with
    | agg vs' =>
      obtain ⟨vs, rfl, hc⟩ := retype_eq_agg hr
      obtain ⟨t', ht'⟩ := hc i
      simp only [valPath] at h ⊢
      rw [ht']
      exact zeroV_path_retype ps t' h
    | _ => simp only [valPath]; exact .poison

theorem valPath_select (ps : List Nat) (i : Nat) (d : Val) :
    valPath ps (Comp.select i [d]) = valPath (i :: ps) d := by
  cases d <;> simp [Comp.select, valPath, valPath_poison]

section
variable {tabs : Tables} {f : Func} {ρ : ID → Val}

/-! ## Fresh malloc calls -/

/-- A register of a fresh malloc call (`freshCall`, issue #69): `poison`, or a tuple whose first
component is the word of a pointer to a heap block whose bytes are all zero in its second
component, a memory. -/
def FreshReg (y : Val) : Prop :=
  y = .poison ∨ ∃ (p : Ptr) (k : Nat) (M : Mem) (rest : List Val),
    y = .tuple (p.word :: .mem M :: rest) ∧ p.blk = .heap k ∧ M.BlockZero p.blk

/-- The registers of `f`'s fresh malloc calls are `FreshReg`. -/
def FreshQ (tabs : Tables) (f : Func) (ρ : ID → Val) : Prop :=
  ∀ c, freshCall tabs f c = true → FreshReg (ρ c)

/-- A fresh malloc call is a `StaticLECall` of `f`. -/
theorem freshCall_value {c : ID} (h : freshCall tabs f c = true) :
    ∃ cv, f.value? c = some cv ∧ cv.op = .StaticLECall := by
  unfold freshCall at h
  simp only [Bool.and_eq_true] at h
  have h1 := h.1
  unfold NilCheck.mallocCall at h1
  split at h1
  · next cv hcv =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨cv, hcv, h1.1.1.1⟩
  · cases h1

/-- A fresh malloc call's term at any fuel: `poison` or its register. -/
theorem fresh_den {c : ID} (h : freshCall tabs f c = true) (k : Nat) :
    den f.value? tabs ρ k c = .poison ∨ den f.value? tabs ρ k c = ρ c := by
  obtain ⟨cv, hcv, hop⟩ := freshCall_value h
  cases k with
  | zero => exact .inl rfl
  | succ k => exact .inr (den_succ_atom (not_term_of hcv (by rw [hop]; decide)))

theorem selectN_den {x : ID} {s : Value} (hs : f.value? x = some s) (hop : s.op = .SelectN)
    (hsz : s.args.size = 1) (k : Nat) :
    den f.value? tabs ρ (k + 1) x =
      (Tuple.selectN s.auxInt [den f.value? tabs ρ k s.args[0]!]).retype (tabs.ty s.type) := by
  rw [den_succ_term hs (by rw [hop]; rfl), toList_one hsz, List.map_cons, List.map_nil, hop,
    GoFV.Proof.Rules.opVal_pure (op := Op.SelectN) rfl]
  rfl

/-- **The memory of a fresh malloc call holds its first result's block all zero** (`FreshQ`):
where the memory `SelectN [1] c` denotes `M` and the pointer-shaped `SelectN [0] c` a pointer
word `P`. -/
theorem fresh_blockZero (hQ : FreshQ tabs f ρ) {m b : ID} {s q : Value}
    (hs : f.value? m = some s) (hsop : s.op = .SelectN) (hs1 : s.auxInt = 1)
    (hssz : s.args.size = 1) (hc : freshCall tabs f s.args[0]! = true)
    (hb : f.value? b = some q) (hqop : q.op = .SelectN) (hq0 : q.auxInt = 0)
    (hqsz : q.args.size = 1) (hqc : q.args[0]! = s.args[0]!) (hqt : isPtrTy (tabs.ty q.type) = true)
    {k : Nat} {M : Mem} (hm : den f.value? tabs ρ k m = .mem M)
    {k' : Nat} {P : Ptr} (hp : (den f.value? tabs ρ k' b).asPtrWord = some P) :
    M.BlockZero P.blk := by
  cases k with
  | zero => simp [den] at hm
  | succ k =>
  cases k' with
  | zero => simp [den, Val.asPtrWord] at hp
  | succ k' =>
  rw [selectN_den hs hsop hssz, hs1] at hm
  rw [selectN_den hb hqop hqsz, hq0, hqc] at hp
  obtain ⟨e, he⟩ : ∃ e, tabs.ty q.type = .ptr e := by
    unfold isPtrTy at hqt
    split at hqt
    · exact ⟨_, by assumption⟩
    · cases hqt
  rw [he] at hp
  rcases fresh_den (ρ := ρ) hc k with h0 | h0
  · rw [h0] at hm; simp [Tuple.selectN, Val.retype] at hm
  rcases fresh_den (ρ := ρ) hc k' with h1 | h1
  · rw [h1] at hp; simp [Tuple.selectN, Val.retype, Val.asPtrWord] at hp
  rw [h0] at hm
  rw [h1] at hp
  rcases hQ _ hc with h | ⟨p, kk, M', rest, hr, -, hz⟩
  · rw [h] at hm; simp [Tuple.selectN, Val.retype] at hm
  rw [hr] at hm hp
  simp only [Tuple.selectN] at hm hp
  have hM : M' = M := retype_mem (by simpa using hm)
  subst hM
  have hP : p = P := (Ptr.word_asPtrWord_of (by simpa [Ptr.word_retype_ptr] using hp)).symm
  subst hP
  exact hz

/-- A successful read of a block whose bytes are all zero reads zeros. -/
theorem blockZero_read {M : Mem} {P : Ptr} (hz : M.BlockZero P.blk) {n : Nat} (hn : n ≠ 0)
    {bs : Array Byte} (h : M.read P n = some bs) : bs = Array.replicate n (.b 0) := by
  obtain ⟨a, ha, h1, -, -, rfl⟩ := read_some hn h
  apply Array.ext
  · simp only [Array.size_extract, Array.size_replicate]; omega
  · intro i h1 h2
    rw [Array.getElem_replicate, Array.getElem_extract]
    exact hz a ha _ (Array.getElem_mem _)

/-- A successful non-empty write reads back successfully before it. -/
theorem read_of_write {m m' : Mem} {p : Ptr} {bs : Array Byte} (hw : m.write p bs = some m')
    (hn : bs.size ≠ 0) : ∃ bs0, m.read p bs.size = some bs0 := by
  unfold Mem.write at hw
  have he : bs.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro h'
    exact hn (Array.isEmpty_iff_size_eq_zero.1 h')
  simp only [he, Bool.false_eq_true, ite_false] at hw
  cases ha : m.find? p.blk with
  | none => rw [ha] at hw; cases hw
  | some a =>
    rw [ha] at hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      refine ⟨a.data.extract p.off.toNat (p.off.toNat + bs.size), ?_⟩
      unfold Mem.read
      simp only [beq_iff_eq, hn, ite_false, ha, Option.bind_eq_bind, Option.bind_some]
      rw [if_pos ⟨hc.1.1.2, hc.1.2, hc.2⟩]
    · cases hw

/-- **A `zeroAt` term has a zero component** at every fuel: a constant term below its depth a
value its value refines (`den_fuel_mono`), a selection the component one step deeper of its
argument (`valPath_select`), a `Copy` its argument's, a make op its arguments' (`ecT_make_term`),
each retyped (`zeroV_path_retype`). -/
theorem zeroAt_den : ∀ (n : Nat) (ps : List Nat) (x : ID), zeroAt tabs f n ps x = true →
    ∀ k, ZeroV (valPath ps (den f.value? tabs ρ k x))
  | 0, _, _, h, _ => by simp [zeroAt] at h
  | n + 1, ps, x, h, k => by
    simp only [zeroAt, Bool.or_eq_true] at h
    rcases h with hc | hs
    · split at hc
      · next c hcx =>
        have h2 := den_fuel_mono f.value? tabs ρ k (max k 4) x (Nat.le_max_left _ _)
        rw [termConst_den 4 x c hcx (max k 4) (Nat.le_max_right _ _)] at h2
        exact zeroV_path_of_refines ps h2 (zeroVal_spec hc)
      · cases hc
    cases k with
    | zero => rw [show den f.value? tabs ρ 0 x = .poison from rfl, valPath_poison]; exact .poison
    | succ k =>
    split at hs
    · next v hv =>
      split at hs
      · next i hi =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨ht, hfr, hev⟩ := GoFV.Proof.EC.ec_sel hi
        rw [den_succ_term hv ht, toList_one hs.1, List.map_cons, List.map_nil,
          GoFV.Proof.Rules.opVal_pure hfr, hev]
        apply zeroV_path_retype
        rw [valPath_select]
        exact zeroAt_den n (i :: ps) _ hs.2 k
      · simp only [Bool.or_eq_true] at hs
        rcases hs with hcp | hs
        · simp only [Bool.and_eq_true, beq_iff_eq] at hcp
          obtain ⟨⟨hop, h1⟩, h2⟩ := hcp
          have ht : termOp v.op = true := by rw [hop]; rfl
          have hfr : GoFV.Proof.Rules.frameOp v.op = false := by rw [hop]; rfl
          rw [den_succ_term hv ht, toList_one h1, List.map_cons, List.map_nil,
            GoFV.Proof.Rules.opVal_pure hfr, hop]
          apply zeroV_path_retype
          exact zeroAt_den n ps _ h2 k
        simp only [Bool.and_eq_true] at hs
        obtain ⟨ht, hev⟩ := GoFV.Proof.EC.ecT_make_term hs.1
        have hfr : GoFV.Proof.Rules.frameOp v.op = false := by
          rcases GoFV.Proof.EC.ecT_make_cases hs.1 with h | h | h | h | h | h <;> rw [h] <;> rfl
        rw [den_succ_term hv ht, GoFV.Proof.Rules.opVal_pure hfr, hev]
        apply zeroV_path_retype
        obtain ⟨-, h2⟩ := hs
        cases ps with
        | nil =>
          refine .agg fun d hd => ?_
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hd
          exact zeroAt_den n [] a (List.all_eq_true.1 h2 a ha) k
        | cons i ps' =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
          simp only [valPath]
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
            Array.getElem?_eq_getElem h2.1, Option.map_some, Option.getD_some,
            ← getElem!_pos v.args i h2.1]
          exact zeroAt_den n ps' _ h2.2 k
    · cases hs

/-- **A `zeroConst` denotes a zero value** at every fuel (`zeroAt_den`). -/
theorem zeroConst_den {x : ID} (h : zeroConst tabs f x = true) (k : Nat) :
    ZeroV (den f.value? tabs ρ k x) :=
  zeroAt_den 10 [] x h k

/-- **Zero bytes through a chain** (`zeroChain`): a successful read at the pointer gives zeros,
read through the disjoint writes from the `Zero` that cleared them or from the memory of a fresh
malloc call (`FreshQ`). -/
theorem zeroChain_read (hT : Term.Typed f.value? tabs ρ) (hM : MemAtoms f.value? tabs ρ)
    (hQ : FreshQ tabs f ρ) (hA : ArgAv tabs f ρ) {p : ID} {n : Nat} (hn : n ≠ 0) {kp : Nat} {P : Ptr}
    (hp : (den f.value? tabs ρ kp p).asPtrWord = some P) :
    ∀ (d : Nat) (m : ID), zeroChain tabs f p n d m = true → ∀ {k : Nat} {M : Mem},
      den f.value? tabs ρ k m = .mem M → ∀ {bs : Array Byte}, M.read P n = some bs →
        bs = Array.replicate n (.b 0)
  | 0, _, h, _, _, _, _, _ => by simp [zeroChain] at h
  | d + 1, m, h, k, M, hm, bs, hbs => by
    unfold zeroChain at h
    cases hs : f.value? m with
    | none => rw [hs] at h; cases h
    | some s =>
    rw [hs] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with ((⟨⟨hcop, hcsz⟩, hch⟩ | ⟨⟨⟨hsop, hssz⟩, hdis⟩, hch⟩) |
      ⟨⟨⟨hzop, hzsz⟩, hle⟩, hbase⟩) | ⟨⟨⟨⟨⟨hsel, hs1⟩, hssz⟩, hfc⟩, hpv⟩, hfresh⟩
    · -- a `Copy` of memory
      have ht : termOp s.op = true := by rw [hcop]; rfl
      cases k with
      | zero => simp [den] at hm
      | succ k =>
      rw [den_succ_term hs ht, toList_one hcsz, List.map_cons, List.map_nil, hcop,
        GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy] at hm
      exact zeroChain_read hT hM hQ hA hn hp d _ hch (retype_eq_mem hm) hbs
    · -- a `Store` at a disjoint pointer
      have hmem : memOp s.op = true := by rcases hsop with h | h <;> rw [h] <;> rfl
      cases k with
      | zero => simp [den] at hm
      | succ k =>
      rw [den_succ_atom (not_term_of hs (by rw [memOp_not_term hmem]; decide))] at hm
      obtain ⟨N, hN⟩ := hM m s hs hmem (by rw [hm]; nofun)
      obtain ⟨y, hy, hρs⟩ := hN N (Nat.le_refl _)
      rw [toList_three hssz, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy
      obtain ⟨q, m0, M', hq, hm0, hwr, rfl⟩ := memDef_store hsop hy
      rw [hm] at hρs
      have hMM := retype_mem hρs.symm
      subst hMM
      rw [read_write_sep hwr (by rw [GoFV.Proof.CSE.Mem.encode_size]; exact disjoint_sep hM hA hdis hp hq)]
        at hbs
      exact zeroChain_read hT hM hQ hA hn hp d _ hch hm0 hbs
    · -- the `Zero`
      have hmem : memOp s.op = true := by rw [hzop]; rfl
      cases k with
      | zero => simp [den] at hm
      | succ k =>
      rw [den_succ_atom (not_term_of hs (by rw [memOp_not_term hmem]; decide))] at hm
      obtain ⟨N, hN⟩ := hM m s hs hmem (by rw [hm]; nofun)
      obtain ⟨y, hy, hρs⟩ := hN N (Nat.le_refl _)
      rw [toList_two hzsz, List.map_cons, List.map_cons, List.map_nil] at hy
      obtain ⟨q, m0, M', hq, -, hwr, rfl⟩ := memDef_zero hzop hy
      rw [hm] at hρs
      have hMM := retype_mem hρs.symm
      subst hMM
      -- the pointer: `q` plus the offset
      obtain ⟨k1, q1, h1, e1⟩ := ptrBase_den 8 p _ P hp
      obtain ⟨k2, q2, h2, e2⟩ := ptrBase_den 8 s.args[0]! _ q hq
      have hq12 := baseSame_den hM 8 _ _ hbase h1 h2
      have hP : P = q.add (BitVec.ofNat 64
          ((ptrBase tabs f 8 p).2 - (ptrBase tabs f 8 s.args[0]!).2).toNat) := by
        rw [e1, e2, hq12, ptr_add_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          BitVec.add_comm (ptrBase tabs f 8 s.args[0]!).2, BitVec.sub_add_cancel]
      have hrd := read_write_self hwr
      rw [Array.size_replicate] at hrd
      rw [hP, read_sub hrd (Nat.pos_of_ne_zero hn) hle, Array.extract_replicate] at hbs
      cases hbs
      congr 1
      omega
    · -- the memory of a fresh malloc call
      cases hb : f.value? (ptrBase tabs f 8 p).1 with
      | none => rw [hb] at hfresh; cases hfresh
      | some q =>
      rw [hb] at hfresh
      simp only [Bool.and_eq_true, beq_iff_eq] at hfresh
      obtain ⟨⟨⟨hqop, hq0⟩, hqsz⟩, hqc⟩ := hfresh
      have hqt : isPtrTy (tabs.ty q.type) = true := by
        unfold ptrVal at hpv; rw [hb] at hpv; exact hpv
      obtain ⟨k1, q1, h1, e1⟩ := ptrBase_den 8 p _ P hp
      have hz := fresh_blockZero hQ hs hsel hs1 hssz hfc hb hqop hq0 hqsz hqc hqt hm h1
      rw [e1] at hbs
      exact blockZero_read (by simpa [Ptr.add] using hz) hn hbs

theorem dropOK_spec {g : Func} {u w : Value} (h : dropOK tabs f g u w = true) :
    w.op = .Copy ∧ w.args.size = 1 ∧ (u.op = .Store ∨ u.op = .Zero) ∧ ∃ i < u.args.size,
      memReach tabs f g u.args[i]! w.args[0]! = true := by
  unfold dropOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, hs⟩, (⟨⟨⟨hop, hsz⟩, hcr⟩, -⟩ | ⟨⟨hop, hsz⟩, (⟨hcr, -⟩ | ⟨hcr, -⟩)⟩)⟩ := h
  · exact ⟨hc, hs, .inl hop, 2, by omega, hcr⟩
  · exact ⟨hc, hs, .inr hop, 1, by omega, by simp [memReach, hcr]⟩
  · exact ⟨hc, hs, .inr hop, 1, by omega, hcr⟩

/-- A memory refined by a value is a memory. -/
theorem refines_mem' {M : Mem} {v : Val} (h : Sem.Refines (.mem M) v) :
    ∃ M', v = .mem M' ∧ Mem.Refines M M' := by
  cases h with
  | mem h => exact ⟨_, rfl, h⟩

/-- **A dropped write is refined by its memory** (`dropOK`): the root's memory is refined by
the memory of `w`'s argument in `f`, or (`memCopyReach` in `g`) by the memory of the root's
memory argument, from which `w`'s argument copies in `g`. -/
theorem drop_mem (hT : Term.Typed f.value? tabs ρ) (hM : MemAtoms f.value? tabs ρ)
    (hQ : FreshQ tabs f ρ) (hA : ArgAv tabs f ρ) {g : Func} {u w : Value} (h : dropOK tabs f g u w = true) {k : Nat}
    {y : Val} (hy : memDef tabs u (u.args.toList.map (den f.value? tabs ρ k)) = some y) :
    ∃ M1, y = .mem M1 ∧
      ((∃ i < u.args.size, copyReach tabs f.valueTab f.valueTab.size u.args[i]! w.args[0]! = true ∧
          ∃ M0, den f.value? tabs ρ k w.args[0]! = .mem M0 ∧ Mem.Refines M1 M0) ∨
        ∃ i < u.args.size, memCopyReach g g.valueTab.size u.args[i]! w.args[0]! = true ∧
          ∃ M0, den f.value? tabs ρ k u.args[i]! = .mem M0 ∧ Mem.Refines M1 M0) := by
  -- a write that changes nothing, of a memory `w`'s argument holds (`memReach`)
  have reach : ∀ {i : Nat} {M1 m0 : Mem}, i < u.args.size →
      memReach tabs f g u.args[i]! w.args[0]! = true →
      den f.value? tabs ρ k u.args[i]! = .mem m0 → Mem.Refines M1 m0 →
      (∃ i < u.args.size, copyReach tabs f.valueTab f.valueTab.size u.args[i]! w.args[0]! = true ∧
          ∃ M0, den f.value? tabs ρ k w.args[0]! = .mem M0 ∧ Mem.Refines M1 M0) ∨
        ∃ i < u.args.size, memCopyReach g g.valueTab.size u.args[i]! w.args[0]! = true ∧
          ∃ M0, den f.value? tabs ρ k u.args[i]! = .mem M0 ∧ Mem.Refines M1 M0 := by
    intro i M1 m0 hi hr hm0 hW
    unfold memReach at hr
    rw [Bool.or_eq_true] at hr
    rcases hr with hcr | hcr
    · have hc := copyReach_den (M := f.valueTab) hT _ _ _ hcr k
      rw [show den (Defs.get? f.valueTab) tabs ρ k u.args[i]! = .mem m0 from hm0] at hc
      obtain ⟨m0', hm0', hR⟩ := refines_mem' hc
      exact .inl ⟨i, hi, hcr, m0', hm0', hW.trans hR⟩
    · exact .inr ⟨i, hi, hcr, m0, hm0, hW⟩
  unfold dropOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨-, (⟨⟨⟨hsop, hssz⟩, hcr⟩, hcase⟩ | ⟨⟨hzop, hzsz⟩, (⟨hcr, hcase⟩ | ⟨hcr, hch⟩)⟩)⟩ := h
  · -- a `Store`
    rw [toList_three hssz, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy
    obtain ⟨q, m0, M', hq, hm0, hwr, rfl⟩ := memDef_store (.inl hsop) hy
    refine ⟨M', rfl, reach (by omega) hcr hm0 ?_⟩
    have hsz : (encode (auxTy tabs u.aux) (den f.value? tabs ρ k u.args[1]!)).size =
        (auxTy tabs u.aux).size := GoFV.Proof.CSE.Mem.encode_size _ _
    by_cases h0 : (auxTy tabs u.aux).size = 0
    · -- a zero-sized write changes nothing
      have he : (encode (auxTy tabs u.aux) (den f.value? tabs ρ k u.args[1]!)).isEmpty = true := by
        rw [Array.isEmpty_iff_size_eq_zero, hsz, h0]
      unfold Mem.write at hwr
      simp only [he, ite_true] at hwr
      cases hwr
      exact Mem.Refines.refl _
    rcases hcase with h0' | ⟨hzc, hch⟩
    · exact absurd h0' h0
    obtain ⟨bs0, hrd⟩ := read_of_write hwr (by rw [hsz]; exact h0)
    have hz := zeroChain_read hT hM hQ hA h0 hq 8 _ hch hm0 (by rw [← hsz]; exact hrd)
    subst hz
    refine write_refines_self (Mem.Refines.refl _) hrd hwr ?_
    have := zeros_refine (encode_zero (zeroConst_den (ρ := ρ) hzc k) (auxTy tabs u.aux))
    simpa [BytesRefineA, hsz] using this
  · -- a `Zero` of a `Zero`
    rw [toList_two hzsz, List.map_cons, List.map_cons, List.map_nil] at hy
    obtain ⟨q, m0, M', hq, hm0, hwr, rfl⟩ := memDef_zero hzop hy
    have hc := copyReach_den (M := f.valueTab) hT _ _ _ hcr k
    rw [show den (Defs.get? f.valueTab) tabs ρ k u.args[1]! = .mem m0 from hm0] at hc
    obtain ⟨m0', hm0', hR⟩ := refines_mem' hc
    refine ⟨M', rfl, .inl ⟨1, by omega, hcr, m0', hm0', ?_⟩⟩
    cases hz : f.value? w.args[0]! with
    | none => rw [hz] at hcase; cases hcase
    | some z =>
    rw [hz] at hcase
    simp only [Bool.and_eq_true, beq_iff_eq] at hcase
    obtain ⟨⟨⟨hzz, hz2⟩, hai⟩, hsame⟩ := hcase
    have hmem : memOp z.op = true := by rw [hzz]; rfl
    cases k with
    | zero => simp [den] at hm0
    | succ k =>
    change den f.value? tabs ρ (k + 1) w.args[0]! = _ at hm0'
    rw [den_succ_atom (not_term_of hz (by rw [memOp_not_term hmem]; decide))] at hm0'
    obtain ⟨N, hN⟩ := hM _ z hz hmem (by rw [hm0']; nofun)
    obtain ⟨y2, hy2, hρ2⟩ := hN N (Nat.le_refl _)
    rw [toList_two hz2, List.map_cons, List.map_cons, List.map_nil] at hy2
    obtain ⟨Q, m00, M2, hQ, -, hw2, rfl⟩ := memDef_zero hzz hy2
    rw [hm0'] at hρ2
    have hMM := retype_mem hρ2.symm
    subst hMM
    have hqQ := samePtr_den hM hsame hq hQ
    subst hqQ
    have hrd := read_write_self hw2
    rw [hai] at hrd
    exact write_refines_self hR hrd hwr (BytesRefineA.refl _)
  · -- a `Zero` of zero bytes
    rw [toList_two hzsz, List.map_cons, List.map_cons, List.map_nil] at hy
    obtain ⟨q, m0, M', hq, hm0, hwr, rfl⟩ := memDef_zero hzop hy
    refine ⟨M', rfl, reach (by omega) hcr hm0 ?_⟩
    by_cases h0 : u.auxInt.toInt.toNat = 0
    · have he : (Array.replicate u.auxInt.toInt.toNat (Byte.b 0)).isEmpty = true := by
        rw [Array.isEmpty_iff_size_eq_zero, Array.size_replicate, h0]
      unfold Mem.write at hwr
      simp only [he, ite_true] at hwr
      cases hwr
      exact Mem.Refines.refl _
    obtain ⟨bs0, hrd⟩ := read_of_write hwr (by rw [Array.size_replicate]; exact h0)
    rw [Array.size_replicate] at hrd
    have hz := zeroChain_read hT hM hQ hA h0 hq 8 _ hch hm0 hrd
    subst hz
    exact write_refines_self (Mem.Refines.refl _) (by rw [Array.size_replicate]; exact hrd) hwr
      (BytesRefineA.refl _)

end

end GoFV.Proof.Pass.LoadFwd
