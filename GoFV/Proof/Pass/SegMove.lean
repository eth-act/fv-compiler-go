import GoFV.Proof.Pass.SegChain
import GoFV.Proof.Pass.SegRo
import GoFV.Proof.Pass.SegCall
import GoFV.Proof.Pass.StructStoreMem
import GoFV.Proof.Pass.LoadFwdMem

/-!
# Segments: a `Move` of stores over a zeroed region (issue #69)

`moveSeg_sound` discharges `SegSound` for the move segments (`generic.rules:1978` family,
`RewriteCheck.moveSeg?`): in `f`, `x = Move [n] dst p m` with `m` (or the memory under the
`VarDef` `m`) `Store op1 d1 (… (Store opk dk z))` over `z = Zero [n] p' _`, every `opi` an
`OffPtr [oi]` of `p` and `p'` reaching `p` through copies; in `g`, `x = Store op1' d1 (…
(Store opk' dk z'))` over the fresh `z' = Zero [n] dst m`, the fresh `opi' = OffPtr [oi] dst`.

The source's registers give the stores' memory `M1` as writes at `P + oi` (`P` the word of
`p`) over the zeroed `n` bytes at `P`, so its `n` bytes at `P` are the zeros with the stores'
bytes put in (`read_write_putBytes`), and the `Move`'s memory `Mm` (`M1`, or `M1` with a frame
block poisoned) refines `M1`: the `Move` read bytes refined by those. The target's `Zero` and
stores write the same bytes at `Dst` over `Mm` (`writes_putBytes`), in the `n` bytes the `Move`
wrote, so their `OffPtr`s stay inside the window (`StructStore.inWindow_of_write`).
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE.Mem (Avail)
open GoFV.Proof.AtomSim (Reg rv rv_of evalValue_of_regs regs_of_ok)
open GoFV.Proof.MemCombine (write_find write_spec write_of_valid read_eq_some toNat_add_ofNat
  foldl_set_getElem?)

/-! ## Memory -/

/-- The bytes `bs` with the writes `ws` (offset, bytes) put in, in order. -/
def putAll (bs : Array Byte) (ws : List (Nat × Array Byte)) : Array Byte :=
  ws.foldl (fun A w => putBytes A w.1 w.2) bs

theorem putAll_size (bs : Array Byte) : ∀ ws : List (Nat × Array Byte), (putAll bs ws).size = bs.size
  | [] => rfl
  | w :: ws => by
    unfold putAll
    rw [List.foldl_cons]
    have := putAll_size (putBytes bs w.1 w.2) ws
    unfold putAll at this
    rw [this, putBytes_size]

theorem putAll_snoc (bs : Array Byte) (ws : List (Nat × Array Byte)) (w : Nat × Array Byte) :
    putAll bs (ws ++ [w]) = putBytes (putAll bs ws) w.1 w.2 := by
  unfold putAll; rw [List.foldl_append]; rfl

/-- **A read after a write inside it**: the bytes read with the written ones put in. -/
theorem read_write_putBytes {m m' : Mem} {P : Ptr} {n o : Nat} {R E : Array Byte}
    (hr : m.read P n = some R) (hw : m.write (P.add (BitVec.ofNat 64 o)) E = some m')
    (ho : o + E.size ≤ n) : m'.read P n = some (putBytes R o E) := by
  by_cases hE : E.size = 0
  · have he : E.isEmpty = true := Array.isEmpty_iff_size_eq_zero.2 hE
    unfold Mem.write at hw
    simp only [he, ite_true] at hw
    cases hw
    rw [StructStore.putBytes_empty _ _ hE]; exact hr
  have hn : n ≠ 0 := by omega
  obtain ⟨a, ha, h1, h2, h3, rfl⟩ := (read_eq_some hn).1 hr
  have hoff : (P.add (BitVec.ofNat 64 o)).off.toNat = P.off.toNat + o := by
    rw [MemCombine.Ptr.add_off, toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha' : m.find? (P.add (BitVec.ofNat 64 o)).blk = some a := by
    rw [MemCombine.Ptr.add_blk]; exact ha
  obtain ⟨rfl, -⟩ := write_spec ha' hw
  rw [MemCombine.Ptr.add_blk, hoff]
  refine (read_eq_some hn).2 ⟨_, by rw [CSE.Mem.find?_set, ite_eq_left rfl], ?_, h2, h3, ?_⟩
  · simp only [CSE.Mem.foldl_set_size]; exact h1
  · apply Array.ext_getElem?
    intro j
    have hRs : (a.data.extract P.off.toNat (P.off.toNat + n)).size = n := by
      simp only [Array.size_extract]; omega
    rw [StructStore.putBytes_getElem? (by rw [hRs]; exact ho)]
    dsimp only
    simp only [Array.getElem?_extract, CSE.Mem.foldl_set_size,
      foldl_set_getElem? _ _ _ _ (Nat.le_refl _) (show P.off.toNat + o + E.size ≤ a.data.size by omega)]
    have hC : (P.off.toNat + o ≤ P.off.toNat + j ∧ P.off.toNat + j < P.off.toNat + o + E.size) ↔
        (o ≤ j ∧ j < o + E.size) := by omega
    simp only [hC]
    by_cases hA : o ≤ j ∧ j < o + E.size
    · have hB : j < min (P.off.toNat + n) a.data.size - P.off.toNat := by omega
      simp only [hA, hB, and_self, ite_true]
      congr 1; omega
    · simp only [hA, ite_false, false_and, and_false]

/-- **Writes inside a written buffer**: writing the buffer and then the writes `ws` at their
offsets succeeds, and is the write of the buffer with them put in. -/
theorem writes_putBytes {Mm : Mem} {Dst : Ptr} :
    ∀ (ws : List (Nat × Array Byte)) {A : Array Byte} {T0 : Mem}, Mm.write Dst A = some T0 →
      (∀ w ∈ ws, w.1 + w.2.size ≤ A.size) →
      ∃ T, writes Dst T0 ws = some T ∧ Mm.write Dst (putAll A ws) = some T
  | [], _, T0, hw, _ => ⟨T0, rfl, hw⟩
  | (o, E) :: ws, A, T0, hw, hin => by
    obtain ⟨T1, h1, h2⟩ := StructStore.write_putBytes hw (hin _ List.mem_cons_self)
    obtain ⟨T, h3, h4⟩ := writes_putBytes ws h2 fun w hw' => by
      rw [putBytes_size]; exact hin w (List.mem_cons_of_mem _ hw')
    refine ⟨T, ?_, h4⟩
    rw [writes, h1, Option.bind_some]; exact h3

/-! ## Evaluations -/

private theorem prio_move : prio .Move ≠ 0 := by decide

/-- A `Move`'s evaluation from its argument registers: the read at its source word written at its
destination word. -/
theorem move_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {d p m : ID} {dv pv mv y : Val}
    (hop : v.op = .Move) (ha : v.args.toList = [d, p, m]) (hd : fr.regs[d]? = some (some dv))
    (hp : fr.regs[p]? = some (some pv)) (hm : fr.regs[m]? = some (some mv))
    (h : evalValue env ctx fr v = .ok y) :
    ∃ Dst P Mm R Ms, dv.asPtrWord = some Dst ∧ pv.asPtrWord = some P ∧ mv = .mem Mm ∧
      Mm.read P v.auxInt.toInt.toNat = some R ∧ Mm.write Dst R = some Ms ∧
      y = (Val.mem Ms).retype (ctx.tys[v.id]?.getD .other) := by
  obtain ⟨argv, r, hargs, ho, rfl⟩ := CSE.Mem.evalValue_ok h
  have hv : v.args = #[d, p, m] := Array.ext' ha
  have : argv = [dv, pv, mv] := CSE.Mem.map_some_inj (by rw [← hargs, hv]; simp [hd, hp, hm])
  subst this
  have ho' : memRoot ctx v [dv, pv, mv] = .ok r := by
    rw [show evalOp env ctx fr v [dv, pv, mv] (ctx.tys[v.id]?.getD .other) =
      memRoot ctx v [dv, pv, mv] by simp only [evalOp, hop]] at ho
    exact ho
  obtain ⟨Dst, P, Mm, R, Ms, hD, hP, rfl, hr, hw, rfl⟩ := memRoot_move hop ho'
  exact ⟨Dst, P, Mm, R, Ms, hD, hP, rfl, hr, hw, rfl⟩

/-- A `VarDef`'s evaluation: its memory with a block poisoned. -/
theorem varDef_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {m : ID} {mv : Val} {y : Val}
    (hop : v.op = .VarDef) (ha : v.args = #[m]) (hm : fr.regs[m]? = some (some mv))
    (h : evalValue env ctx fr v = .ok y) :
    ∃ M b, mv = .mem M ∧ y = (Val.mem (M.poisonBlock b)).retype (ctx.tys[v.id]?.getD .other) := by
  obtain ⟨argv, r, hargs, ho, rfl⟩ := CSE.Mem.evalValue_ok h
  have : argv = [mv] := CSE.Mem.map_some_inj (by rw [← hargs, ha]; simp [hm])
  subst this
  have ho' : memRoot ctx v [mv] = .ok r := by
    rw [show evalOp env ctx fr v [mv] (ctx.tys[v.id]?.getD .other) =
      memRoot ctx v [mv] by simp only [evalOp, hop]] at ho
    exact ho
  simp only [memRoot, hop] at ho'
  cases mv with
  | mem M =>
    simp only at ho'
    split at ho'
    · cases ho'; exact ⟨M, _, rfl, rfl⟩
    · cases ho'
  | _ => simp at ho' <;> (split at ho' <;> cases ho')

/-- A `Zero` evaluates to its write at its address word. -/
theorem zero_eval {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {q m : ID} {Q : Ptr}
    {qv : Val} {M M' : Mem} (hop : v.op = .Zero) (ha : v.args = #[q, m])
    (hq : fr.regs[q]? = some (some qv)) (hQ : qv.asPtrWord = some Q)
    (hm : fr.regs[m]? = some (some (.mem M)))
    (hw : M.write Q (Array.replicate v.auxInt.toInt.toNat (.b 0)) = some M') :
    evalValue env ctx fr v = .ok ((Val.mem M').retype (ctx.tys[v.id]?.getD .other)) := by
  rw [evalValue_of_regs (fun a ha' => by
      rw [ha] at ha'
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · exact ⟨_, hq⟩
      · exact ⟨_, hm⟩), CSE.Mem.evalOp_memRoot (.inr hop)]
  have hl : v.args.toList.map (rv fr) = [qv, .mem M] := by
    rw [ha]; simp [rv_of hq, rv_of hm]
  rw [hl]
  simp only [memRoot, hop, hQ, hw, writeRes]
  rfl

/-- A fresh `OffPtr [o] dst` of pointer shape, `dst` holding a word of `Dst` and `Dst + o` inside
its window, evaluates to a word of `Dst + o`. -/
theorem offPtr_eval {env : Env} {tabs : Tables} {g : Func} {fr : Frame} {q d : ID} {qv : Value}
    {dv : Val} {Dst : Ptr} (hq : g.value? q = some qv) (hid : qv.id = q) (hop : qv.op = .OffPtr)
    (ha : qv.args = #[d]) (hty : isPtrTy (tabs.ty qv.type) = true) (h0 : 0 ≤ qv.auxInt.toInt)
    (hd : fr.regs[d]? = some (some dv)) (hD : dv.asPtrWord = some Dst)
    (hin : (Dst.add (BitVec.ofNat 64 qv.auxInt.toInt.toNat)).inWindow = true) :
    ∃ y, evalValue env (Ctx.make tabs g) fr qv = .ok y ∧
      y.asPtrWord = some (Dst.add (BitVec.ofNat 64 qv.auxInt.toInt.toNat)) := by
  have hreg : ∀ b ∈ qv.args, Reg fr b := fun b hb => by
    rw [ha] at hb; simp only [List.mem_toArray, List.mem_singleton] at hb; subst hb
    exact ⟨_, hd⟩
  rw [evalValue_of_regs hreg, AtomSim.evalOp_term (by rw [hop]; decide),
    GoFV.Proof.Rules.opVal_pure (by rw [hop]; decide), hop, StructStore.evalPure_offPtr, ha]
  simp only [List.map_toArray, List.map_cons, List.map_nil, rv_of hd]
  rw [hid, Proof.tys_of_value hq]
  refine ⟨_, rfl, ?_⟩
  generalize tabs.ty qv.type = ty at hty ⊢
  cases ty <;> simp [isPtrTy] at hty
  have hai : BitVec.ofInt 64 qv.auxInt.toInt = BitVec.ofNat 64 qv.auxInt.toInt.toNat := by
    rw [← Int.toNat_of_nonneg h0]; simp
  rw [Option.getD_some, Val.asPtrWord_retype_ptr, PtrOps.offPtr_asPtrWord, hD, Option.bind_some,
    hai, Ptr.step?, ite_eq_left hin]

/-! ## The validator's facts -/

theorem moveStoreOK_spec {tabs : Tables} {f g : Func} {p dst : ID} {n : Int64} {b : ID}
    {sa sb : Value} (h : moveStoreOK tabs f g p dst n b sa sb = true) :
    sa.op = .Store ∧ sb.op = .Store ∧ sa.args.size = 3 ∧ sb.args.size = 3 ∧ sb.aux = sa.aux ∧
      sb.type = sa.type ∧ sb.args[1]! = sa.args[1]! ∧ sa.block = b ∧ sb.block = b ∧
      0 < (auxTy tabs sa.aux).size ∧ f.value? sb.args[0]! = none ∧
      ∃ q q', f.value? sa.args[0]! = some q ∧ g.value? sb.args[0]! = some q' ∧
        q.op = .OffPtr ∧ q.args.size = 1 ∧ isPtrTy (tabs.ty q.type) = true ∧
        samePtr tabs f q.args[0]! p = true ∧
        q'.op = .OffPtr ∧ q'.args = #[dst] ∧ q'.auxInt = q.auxInt ∧
        isPtrTy (tabs.ty q'.type) = true ∧ 0 ≤ q.auxInt.toInt ∧
        q.auxInt.toInt + (auxTy tabs sa.aux).size ≤ n.toInt := by
  unfold moveStoreOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  split at h12
  · rename_i q q' hq hq'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h12
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩ := h12
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, q, q', hq, hq', k1, k2, k3, k4, k5, k6, k7,
      k8, k9, k10⟩
  · cases h12

/-! ## The chains -/

/-- `gs` are values of `g` from `t` down their last arguments, over `z'`. -/
def GChain (g : Func) : ID → List ID → ID → Prop
  | t, [], z' => t = z'
  | t, u :: us, z' => u = t ∧ ∃ uv, g.value? t = some uv ∧ GChain g (lastArg uv) us z'

theorem fchain_gchain {f g : Func} : ∀ {t m0 z' : ID} {ns : List ID},
    FChain f g t (ns ++ [z']) m0 → GChain g t ns z'
  | _, _, _, [], h => by obtain ⟨h1, -⟩ := h; exact h1.symm
  | _, _, _, _ :: _, ⟨h1, _, uv, huv, h⟩ => ⟨h1, uv, huv, fchain_gchain h⟩

theorem fchain_last {f g : Func} : ∀ {t m0 z' : ID} {ns : List ID},
    FChain f g t (ns ++ [z']) m0 → ∃ zv, g.value? z' = some zv ∧ f.value? z' = none ∧
      lastArg zv = m0
  | _, _, _, [], ⟨h1, hf, zv, hzv, h⟩ => by subst h1; exact ⟨zv, hzv, hf, h⟩
  | _, _, _, _ :: _, ⟨_, _, _, _, h⟩ => fchain_last h

theorem fchain_fresh {f g : Func} : ∀ {t m0 : ID} {ns : List ID},
    FChain f g t ns m0 → ∀ u ∈ ns, f.value? u = none
  | _, _, [], _, u, hu => absurd hu List.not_mem_nil
  | _, _, _ :: _, ⟨rfl, hf, _, _, h⟩, u, hu => by
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hf
    · exact fchain_fresh h u hu

/-- Every value of `gs` has its pair in `fs` when the lists are as long. -/
theorem zip_all_right {P : ID × ID → Bool} : ∀ {fs gs : List ID},
    (fs.zip gs).all P = true → fs.length = gs.length → ∀ b ∈ gs, ∃ a, P (a, b) = true
  | [], [], _, _, b, hb => absurd hb List.not_mem_nil
  | a :: fs, c :: gs, h, hl, b, hb => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, h.1⟩
    · exact zip_all_right h.2 (by simpa using hl) b hb
  | [], _ :: _, _, hl, _, _ => by cases hl
  | _ :: _, [], _, hl, _, _ => by cases hl

/-- The `OffPtr`s of the target's stores hold words of `Dst` plus their offsets. -/
def OffOK (g : Func) (Dst : Ptr) (Fr : Frame) (gs : List ID) : Prop :=
  ∀ b ∈ gs, ∀ sb q', g.value? b = some sb → g.value? sb.args[0]! = some q' → q'.op = .OffPtr →
    ∃ y, Fr.regs[sb.args[0]!]? = some (some y) ∧
      y.asPtrWord = some (Dst.add (BitVec.ofNat 64 q'.auxInt.toInt.toNat))

/-- Setting a register that is no `OffPtr` keeps `OffOK`. -/
theorem OffOK.set_other {g : Func} {Dst : Ptr} {Fr : Frame} {gs : List ID} (h : OffOK g Dst Fr gs)
    {t : ID} {tv : Value} (htv : g.value? t = some tv) (hop : tv.op ≠ .OffPtr) (y : Val) :
    OffOK g Dst (Fr.set t y) gs := by
  intro b hb sb q' hsb hq' hqop
  have hne : t ≠ sb.args[0]! := by
    rintro he; rw [← he, htv] at hq'; cases hq'; exact hop hqop
  rw [Proof.Frame.set_regs_ne hne]
  exact h b hb sb q' hsb hq' hqop

/-- Setting an `OffPtr`'s register to a word of `Dst` plus its offset keeps `OffOK`. -/
theorem OffOK.set_off {g : Func} {Dst : Ptr} {Fr : Frame} {gs : List ID} (h : OffOK g Dst Fr gs)
    {q : ID} {qv : Value} (hqv : g.value? q = some qv) {y : Val} (hlt : q < Fr.regs.size)
    (hy : y.asPtrWord = some (Dst.add (BitVec.ofNat 64 qv.auxInt.toInt.toNat))) :
    OffOK g Dst (Fr.set q y) gs := by
  intro b hb sb q' hsb hq' hqop
  by_cases he : q = sb.args[0]!
  · rw [← he, hqv] at hq'; cases hq'
    rw [← he]; exact ⟨y, Proof.Frame.set_regs_self hlt, hy⟩
  · rw [Proof.Frame.set_regs_ne he]
    exact h b hb sb q' hsb hq' hqop

section
variable {env : Env} {tabs : Tables} {f g : Func} {S : Frame} {A : ID → Prop}

/-- **The fresh `OffPtr`s**: those of the stores `L` evaluate (in `L`'s order) from a frame that
agrees with the source's on the available values, to words of `Dst` plus their offsets. -/
theorem eval_offs (H : Avail env tabs f S A) {d : ID} {dv : Val} {Dst : Ptr} (hdA : A d)
    (hdv : S.regs[d]? = some (some dv)) (hD : dv.asPtrWord = some Dst) :
    ∀ (L : List ID), (∀ b ∈ L, ∀ sb, g.value? b = some sb → ∃ qv, g.value? sb.args[0]! = some qv ∧
        qv.id = sb.args[0]! ∧ qv.op = .OffPtr ∧ qv.args = #[d] ∧
        isPtrTy (tabs.ty qv.type) = true ∧ 0 ≤ qv.auxInt.toInt ∧
        (Dst.add (BitVec.ofNat 64 qv.auxInt.toInt.toNat)).inWindow = true ∧
        f.value? sb.args[0]! = none) →
      ∀ Fr : Frame, (∀ a, A a → Fr.regs[a]? = S.regs[a]?) → g.valueTab.size ≤ Fr.regs.size →
      ∃ Fr', evalAll env (Ctx.make tabs g) Fr (L.filterMap fun b => (g.value? b).map (·.args[0]!))
          = .ok Fr' ∧ (∀ a, A a → Fr'.regs[a]? = S.regs[a]?) ∧ g.valueTab.size ≤ Fr'.regs.size ∧
        OffOK g Dst Fr' L ∧ (∀ L', OffOK g Dst Fr L' → OffOK g Dst Fr' L')
  | [], _, Fr, hag, hsz => ⟨Fr, rfl, hag, hsz, fun _ h => absurd h List.not_mem_nil, fun _ h => h⟩
  | b :: L, hL, Fr, hag, hsz => by
    cases hb : g.value? b with
    | none =>
      obtain ⟨Fr', h1, h2, h3, h4, h5⟩ := eval_offs H hdA hdv hD L
        (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')) Fr hag hsz
      refine ⟨Fr', by simpa [List.filterMap_cons, hb] using h1, h2, h3, fun b' hb' => ?_, h5⟩
      rcases List.mem_cons.1 hb' with rfl | hb'
      · intro sb q' hsb; rw [hb] at hsb; cases hsb
      · exact h4 b' hb'
    | some sb =>
      obtain ⟨qv, hqv, hqid, hqop, hqa, hqty, h0, hin, hqf⟩ := hL b List.mem_cons_self sb hb
      obtain ⟨y, hy, hyw⟩ := offPtr_eval (env := env) (tabs := tabs) (fr := Fr) hqv hqid hqop hqa
        hqty h0 (by rw [hag d hdA]; exact hdv) hD hin
      have hlt : sb.args[0]! < Fr.regs.size :=
        Nat.lt_of_lt_of_le (CheckFacts.lt_of_value? hqv) hsz
      have hag1 : ∀ a, A a → (Fr.set sb.args[0]! y).regs[a]? = S.regs[a]? := fun a ha => by
        have hne : sb.args[0]! ≠ a := by
          rintro rfl
          obtain ⟨_, _, hv, -⟩ := H.val _ ha
          rw [hqf] at hv; cases hv
        rw [Proof.Frame.set_regs_ne hne, hag a ha]
      obtain ⟨Fr', h1, h2, h3, h4, h5⟩ := eval_offs H hdA hdv hD L
        (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')) (Fr.set sb.args[0]! y) hag1
        (by simpa [Frame.set] using hsz)
      refine ⟨Fr', ?_, h2, h3, fun b' hb' => ?_, fun L' hL' => h5 L' (hL'.set_off hqv hlt hyw)⟩
      · rw [List.filterMap_cons, hb]
        simp only [Option.map_some]
        rw [Proof.evalAll_cons]
        simp only [Proof.stepV, show (Ctx.make tabs g).f = g from rfl, hqv, hy]
        exact h1
      · rcases List.mem_cons.1 hb' with rfl | hb'
        · intro sb' q' hsb hq' hqop'
          rw [hb] at hsb; cases hsb
          rw [hqv] at hq'; cases hq'
          have : OffOK g Dst (Fr.set sb.args[0]! y) [b'] := by
            intro b'' hb'' sb'' q'' hsb'' hq'' _
            simp only [List.mem_singleton] at hb''; subst hb''
            rw [hb] at hsb''; cases hsb''
            rw [hqv] at hq''; cases hq''
            exact ⟨y, Proof.Frame.set_regs_self hlt, hyw⟩
          exact h5 _ this _ List.mem_cons_self _ _ hb hqv hqop'
        · exact h4 b' hb'

/-- Values that `samePtr` relates hold the same register. -/
theorem samePtr_reg (H : Avail env tabs f S A) (hT : Proof.Typed (Ctx.make tabs f) S)
    (hid : ∀ z v, A z → f.value? z = some v → v.id = z) {a b : ID} (ha : A a) (hb : A b)
    (h : samePtr tabs f a b = true) : S.regs[a]? = S.regs[b]? := by
  obtain ⟨hcaA, h1⟩ := StructStore.copy_reg H hT hid f.valueTab.size ha
    (StructStore.copyReach_copyEnd _ f.valueTab.size a)
  obtain ⟨hcbA, h2⟩ := StructStore.copy_reg H hT hid f.valueTab.size hb
    (StructStore.copyReach_copyEnd _ f.valueTab.size b)
  rw [← h1, ← h2]
  unfold samePtr at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · rw [h]
  generalize copyEnd tabs f.valueTab f.valueTab.size a = ca at hcaA h
  generalize copyEnd tabs f.valueTab f.valueTab.size b = cb at hcbA h
  cases hva : f.value? ca with
  | none => rw [hva] at h; simp at h
  | some va =>
  cases hvb : f.value? cb with
  | none => rw [hva, hvb] at h; simp at h
  | some vb =>
  rw [hva, hvb] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨⟨hopa, hopb⟩, n, hn⟩, hax⟩, htyv⟩ := h
  have hval : ∀ {c v}, A c → f.value? c = some v → v.op = .LocalAddr → v.aux = some n →
      S.regs[c]? = some (some ((Val.ptr ⟨frameBlk (Ctx.make tabs f).tabs (Ctx.make tabs f).act n, 0⟩).retype
        (tabs.ty v.type))) := by
    intro c v hc hv hop hx
    obtain ⟨y, hy⟩ := Avail.reg H hc
    have hev := Avail.eval H hc hv (by rw [hop]; decide) hy
    rw [evalValue_of_regs (regs_of_ok hev), CSE.Mem.evalOp_frameVal (.inr hop)
      (by simp only [frameVal, hop, hx]; rfl)] at hev
    simp only [Res.bind_ok, Res.ok.injEq] at hev
    rw [hid c v hc hv, Proof.tys_of_value hv, Option.getD_some] at hev
    rw [hy, ← hev]
  rw [hval hcaA hva hopa hn, hval hcbA hvb hopb (by rw [← hax]; exact hn), htyv]

/-- **The stores below the anchor**: if the source's stores from `s` (over `z`) evaluated to `M`,
its `n` bytes at `P` are the zeros with the stores' bytes `ws` put in (bottom first), and the
target's stores from `t` (over `z'`) evaluate to the writes `ws` at `Dst` over `z'`'s memory. -/
theorem move_below (H : Avail env tabs f S A) (hT : Proof.Typed (Ctx.make tabs f) S)
    (hid : ∀ z v, A z → f.value? z = some v → v.id = z) {pz z z' dst b : ID} {P Dst : Ptr}
    {pv : Val} {n : Int64} (hpA : A pz) (hP : S.regs[pz]? = some (some pv))
    (hpv : pv.asPtrWord = some P)
    (hz : ∀ M, S.regs[z]? = some (some (.mem M)) → A z →
      M.read P n.toInt.toNat = some (Array.replicate n.toInt.toNat (.b 0))) :
    ∀ (fs gs : List ID) (s t : ID) (M : Mem), SChain f s fs z → GChain g t gs z' →
      fs.length = gs.length → (∀ u ∈ gs, ∀ v, g.value? u = some v → v.id = u) →
      (fs.zip gs).all (fun (a, c) => match f.value? a, g.value? c with
        | some sa, some sb => moveStoreOK tabs f g pz dst n b sa sb
        | _, _ => false) = true →
      S.regs[s]? = some (some (.mem M)) → A s →
      ∃ ws, M.read P n.toInt.toNat = some (putAll (Array.replicate n.toInt.toNat (.b 0)) ws) ∧
        (∀ w ∈ ws, w.1 + w.2.size ≤ n.toInt.toNat) ∧
        (∃ Mz, S.regs[z]? = some (some (.mem Mz)) ∧ A z) ∧
        ∀ Tz T, writes Dst Tz ws = some T →
        ∀ Fr : Frame, (∀ a, A a → Fr.regs[a]? = S.regs[a]?) → g.valueTab.size ≤ Fr.regs.size →
          OffOK g Dst Fr gs → Fr.regs[z']? = some (some (.mem Tz)) →
          (∀ u ∈ gs, f.value? u = none) →
          ∃ Fr', evalAll env (Ctx.make tabs g) Fr gs.reverse = .ok Fr' ∧
            Fr'.regs[t]? = some (some (.mem T)) ∧ (∀ a, A a → Fr'.regs[a]? = S.regs[a]?) ∧
            g.valueTab.size ≤ Fr'.regs.size ∧ (∀ L, OffOK g Dst Fr L → OffOK g Dst Fr' L)
  | [], gs, s, t, M, hsc, hgc, hlen, _, _, hM, hA => by
    cases gs with
    | cons _ _ => cases hlen
    | nil =>
    have hs : s = z := hsc
    have ht : t = z' := hgc
    subst hs ht
    refine ⟨[], hz M hM hA, by simp, ⟨M, hM, hA⟩, fun Tz T hW Fr hag hsz _ hz' _ => ?_⟩
    cases hW
    exact ⟨Fr, rfl, hz', hag, hsz, fun _ h => h⟩
  | s' :: fs1, gs, s, t, M, hsc, hgc, hlen, hgid, hzip, hM, hA => by
    cases gs with
    | nil => cases hlen
    | cons t' gs1 =>
    obtain ⟨hs', sv, hs, hop, hsz3, hsc1⟩ := hsc
    subst s'
    obtain ⟨ht', tv, htv, hgc1⟩ := hgc
    subst t'
    simp only [List.zip_cons_cons, List.all_cons, hs, htv, Bool.and_eq_true] at hzip
    obtain ⟨hpair, hzip1⟩ := hzip
    obtain ⟨hsop, htop, hsa, hta, haux, htype, hval, -, -, hszp, hqf, q, q', hq, hq', hqop, hqa,
      hqty, hce, hq'op, hq'a, hq'ai, hq'ty, h0, hle⟩ := moveStoreOK_spec hpair
    -- the source's store
    have ha := CSE.Mem.args_three hsa
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
    obtain ⟨Q, M1, M2, hQ, rfl, hw, rfl⟩ := store_ok hop ha hqv hxv hmv (hev (by rw [hop]; decide))
    change M1.write _ (encode (auxTy tabs sv.aux) xv) = some M2 at hw
    have ho : q.auxInt.toInt = ((q.auxInt.toInt.toNat : Nat) : Int) := (Int.toNat_of_nonneg h0).symm
    have hqcA : A q.args[0]! := H.cl _ q hA0 hq (by rw [hqop]; decide) _
      (by rw [StructStore.args1 hqa]; simp)
    have hQe := offPtr_reg_of H hid hA0 hq hqop hqa ho hqty
      (samePtr_reg H hT hid hqcA hpA hce) hP hpv hqv hQ
    subst hQe
    rw [hid s sv hA hs, Proof.tys_of_value hs, Option.getD_some, hM] at hy
    obtain ⟨hty, rfl⟩ := retype_mem_eq (Option.some.inj (Option.some.inj hy)).symm
    obtain ⟨ws1, hr1, hin1, hMz, htg⟩ := move_below H hT hid hpA hP hpv hz fs1 gs1 sv.args[2]!
      (lastArg tv) M1 hsc1 hgc1 (by simpa using hlen)
      (fun u hu => hgid u (List.mem_cons_of_mem _ hu)) hzip1 hmv hA2
    have he : (encode (auxTy tabs sv.aux) xv).size = (auxTy tabs sv.aux).size := Sem.encode_size _ _
    have hle' : q.auxInt.toInt.toNat + (auxTy tabs sv.aux).size ≤ n.toInt.toNat := by omega
    refine ⟨ws1 ++ [(q.auxInt.toInt.toNat, encode (auxTy tabs sv.aux) xv)], ?_, ?_, hMz, ?_⟩
    · rw [putAll_snoc]
      exact read_write_putBytes hr1 hw (by rw [he]; exact hle')
    · intro w hw'
      rcases List.mem_append.1 hw' with hw' | hw'
      · exact hin1 w hw'
      · simp only [List.mem_singleton] at hw'; subst hw'
        show q.auxInt.toInt.toNat + (encode (auxTy tabs sv.aux) xv).size ≤ _
        rw [he]; exact hle'
    intro Tz T hW Fr hag hfsz hoff hz' hnew
    obtain ⟨W1, hW1, hw1⟩ := writes_snoc hW
    obtain ⟨Fr1, he1, hr1', hag1, hsz1, hoff1⟩ := htg Tz W1 hW1 Fr hag hfsz
      (fun b hb => hoff b (List.mem_cons_of_mem _ hb)) hz'
      (fun u hu => hnew u (List.mem_cons_of_mem _ hu))
    -- the target's store `t`
    have hoffT := hoff1 _ hoff t List.mem_cons_self tv q' htv hq' hq'op
    obtain ⟨yq, hyq, hyqw⟩ := hoffT
    rw [hq'ai] at hyqw
    have hta' : tv.args = #[tv.args[0]!, sv.args[1]!, lastArg tv] := by
      rw [lastArg_three hta, ← hval]; exact CSE.Mem.args_three hta
    have hev := store_eval (env := env) (ctx := Ctx.make tabs g) htop hta' hyq hyqw
      (by rw [hag1 _ hA1]; exact hxv) hr1'
      (by rw [show (Ctx.make tabs g).tabs = tabs from rfl, haux]; exact hw1)
    rw [hgid t List.mem_cons_self tv htv, Proof.tys_of_value htv, Option.getD_some, htype, hty]
      at hev
    have htlt : t < Fr1.regs.size := Nat.lt_of_lt_of_le (CheckFacts.lt_of_value? htv) hsz1
    refine ⟨Fr1.set t (.mem T), ?_, Proof.Frame.set_regs_self htlt, fun a ha' => ?_, ?_,
      fun L hL => (hoff1 L hL).set_other htv (by rw [htop]; decide) _⟩
    · rw [List.reverse_cons, Proof.evalAll_append, he1]
      dsimp only
      rw [Proof.evalAll_cons]
      simp only [Proof.stepV, show (Ctx.make tabs g).f = g from rfl, htv, hev]
      rfl
    · have hne : t ≠ a := by
        rintro rfl
        obtain ⟨_, _, hv, -⟩ := H.val t ha'
        rw [hnew t List.mem_cons_self] at hv
        cases hv
      rw [Proof.Frame.set_regs_ne hne, hag1 a ha']
    · simpa [Frame.set] using hsz1
end

/-- What `moveSeg?` says. -/
theorem moveSeg_spec {tabs : Tables} {f g : Func} {x : ID} {fv gv : Value} {D N : List ID}
    (h : moveSeg? tabs f g x fv gv = some (D, N)) :
    D = [] ∧ fv.op = .Move ∧ ∃ d p m m1 ns z' fs z zv zv', fv.args.toList = [d, p, m] ∧
      (m1 = m ∨ ∃ mv : Value, f.value? m = some mv ∧ mv.op = .VarDef ∧ mv.args = #[m1]) ∧
      FChain f g (lastArg gv) (ns ++ [z']) m ∧ storesF f (ns.length + 1) m1 = some (fs, z) ∧
      f.value? z = some zv ∧ g.value? z' = some zv' ∧ gv.op = .Store ∧ 0 ≤ fv.auxInt.toInt ∧
      zv.op = .Zero ∧ zv.args.size = 2 ∧ zv.auxInt = fv.auxInt ∧
      samePtr tabs f zv.args[0]! p = true ∧
      zv'.op = .Zero ∧ zv'.args = #[d, m] ∧ zv'.auxInt = fv.auxInt ∧ zv'.type = zv.type ∧
      (fs.zip (x :: ns)).all (fun (a, b) => match f.value? a, g.value? b with
        | some sa, some sb => moveStoreOK tabs f g p d fv.auxInt fv.block sa sb
        | _, _ => false) = true ∧
      N = ((x :: ns).filterMap fun b => (g.value? b).map (·.args[0]!)) ++ z' :: ns.reverse := by
  unfold moveSeg? at h
  split at h
  case h_2 => cases h
  rename_i d p m hop hargs
  generalize hm1 : underVarDef f m = m1 at h
  have hm1' : m1 = m ∨ ∃ mv : Value, f.value? m = some mv ∧ mv.op = .VarDef ∧ mv.args = #[m1] := by
    unfold underVarDef at hm1
    cases hmv : f.value? m with
    | none => rw [hmv] at hm1; exact .inl hm1.symm
    | some mv =>
      rw [hmv] at hm1
      simp only at hm1
      split at hm1
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact .inr ⟨mv, rfl, hc.1, by rw [StructStore.args1 hc.2, hm1]⟩
      · exact .inl hm1.symm
  generalize hfc : freshChain f g 5 (lastArg gv) = r at h
  obtain ⟨ns0, m0⟩ := r
  simp only at h
  cases hl : ns0.getLast? with
  | none => rw [hl] at h; cases h
  | some z' =>
  rw [hl] at h
  cases hsf : storesF f ns0.length m1 with
  | none => rw [hsf] at h; cases h
  | some r =>
  obtain ⟨fs, z⟩ := r
  rw [hsf] at h
  simp only at h
  cases hzv : f.value? z with
  | none => rw [hzv] at h; cases h
  | some zv =>
  cases hzv' : g.value? z' with
  | none => rw [hzv, hzv'] at h; cases h
  | some zv' =>
  rw [hzv, hzv'] at h
  simp only at h
  split at h
  case isFalse => cases h
  rename_i hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgop, hm0⟩, h0⟩, hzop⟩, hzsz⟩, hzai⟩, hce⟩, hz'op⟩, hz'a⟩, hz'ai⟩, hz'ty⟩,
    hzip⟩ := hc
  obtain ⟨ns, rfl⟩ := List.getLast?_eq_some_iff.1 hl
  have hfc' := freshChain_chain hfc
  rw [hm0] at hfc'
  simp only [List.dropLast_concat] at hzip
  refine ⟨rfl, hop, d, p, m, m1, ns, z', fs, z, zv, zv', hargs, hm1', hfc', ?_, hzv, hzv',
    hgop, h0, hzop, hzsz, hzai, hce, hz'op, hz'a, hz'ai, hz'ty, hzip, ?_⟩
  · simpa using hsf
  · simp [List.dropLast_concat, List.reverse_append]

/-! ## The obligation -/

private theorem retype_mem_mem (M : Mem) : (Val.mem M).retype .mem = .mem M := rfl

/-- **Move segments are sound**: the target's fresh `OffPtr`s, `Zero`, stores and anchor evaluate
from the source frame, and its anchor's memory refines the source's `Move`'s. -/
theorem moveSeg_sound {tabs : Tables} {f g : Func} {x : ID} {fv gv : Value} {D N : List ID}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (h : moveSeg? tabs f g x fv gv = some (D, N))
    (hgid : ∀ n ∈ N ++ [x], ∀ v, g.value? n = some v → v.id = n) (hty : gv.type = fv.type)
    (Q : Mem → Prop) (env : Env) :
    SegSound Q env tabs f g x D N := by
  obtain ⟨rfl, hop, d, p, m, m1, ns, z', fs, z, zv, zv', hfa, hm1, hfc, hsf, hzv, hzv', hgop, h0,
    hzop, hzsz, hzai, hce, hz'op, hz'a, hz'ai, hz'ty, hzip, rfl⟩ := moveSeg_spec h
  have hnphi : fv.op ≠ .Phi := by rw [hop]; decide
  have hroot : CSE.rootNode f x = true := by
    simp only [CSE.rootNode, hfv, Option.map_some, Option.getD_some, hop]; decide
  refine ⟨fun s hs _ sv fr e mm hsv hpan => ?_, fun S A H hT _ hid hsize hroots => ?_⟩
  · simp only [List.nil_append, List.mem_singleton] at hs
    subst hs
    rw [hfv] at hsv; cases hsv
    rcases Proof.evalValue_panic_op hpan with hc | hc <;> rw [hop] at hc <;> revert hc <;> decide
  have hxA : A x := hroots x (by simp) hroot
  have hfa' : fv.args = #[d, p, m] := Array.ext' hfa
  have hcx := H.cl x fv hxA hfv hnphi
  have hdA := hcx d (by rw [hfa']; simp)
  have hpA := hcx p (by rw [hfa']; simp)
  have hmA := hcx m (by rw [hfa']; simp)
  obtain ⟨dv, hdv⟩ := Avail.reg H hdA
  obtain ⟨pv, hpv⟩ := Avail.reg H hpA
  obtain ⟨mv, hmv⟩ := Avail.reg H hmA
  obtain ⟨yx, hyx⟩ := Avail.reg H hxA
  -- the source's `Move`
  obtain ⟨Dst, P, Mm, R, Ms, hD, hP, rfl, hR, hMs, rfl⟩ :=
    move_ok hop hfa hdv hpv hmv (Avail.eval H hxA hfv hnphi hyx)
  have hRs : R.size = fv.auxInt.toInt.toNat := DSE.read_size hR
  -- the stores' memory, which the `Move`'s refines
  obtain ⟨M1, hM1, hm1A, href⟩ : ∃ M1, S.regs[m1]? = some (some (.mem M1)) ∧ A m1 ∧
      Mem.Refines Mm M1 := by
    rcases hm1 with rfl | ⟨mvv, hmvv, hvd, hva⟩
    · exact ⟨Mm, hmv, hmA, Mem.Refines.refl _⟩
    · have hm1A := H.cl m mvv hmA hmvv (by rw [hvd]; decide) m1 (by rw [hva]; simp)
      obtain ⟨y1, hy1⟩ := Avail.reg H hm1A
      have hev := Avail.eval H hmA hmvv (by rw [hvd]; decide) hmv
      obtain ⟨M1, b, rfl, hy⟩ := varDef_ok hvd hva hy1 hev
      rw [hid m mvv hmA hmvv, Proof.tys_of_value hmvv, Option.getD_some] at hy
      obtain ⟨-, hMm⟩ := retype_mem_eq hy.symm
      subst hMm
      exact ⟨M1, hy1, hm1A, poisonBlock_refines M1 b⟩
  -- the chains
  obtain ⟨hsc, hlen⟩ := storesF_chain hsf
  have hgc := fchain_gchain hfc
  obtain ⟨zv'', hzv'', hfz', hlz'⟩ := fchain_last hfc
  rw [hzv'] at hzv''; cases hzv''
  have hnsf : ∀ u ∈ ns, f.value? u = none := fun u hu =>
    fchain_fresh hfc u (List.mem_append_left _ hu)
  cases fs with
  | nil => cases hlen
  | cons m1' fs1 =>
  obtain ⟨hm1', sv1, hsv1, hop1, hsz1, hsc1⟩ := hsc
  subst m1'
  have hzip0 := hzip
  simp only [List.zip_cons_cons, List.all_cons, hsv1, hgv, Bool.and_eq_true] at hzip
  obtain ⟨hpair, hzip1⟩ := hzip
  -- the `Zero`: its memory holds zeros at `P`
  have hz : ∀ M, S.regs[z]? = some (some (.mem M)) → A z → M.read P fv.auxInt.toInt.toNat = some (Array.replicate fv.auxInt.toInt.toNat (.b 0)) := by
    intro M hM hzA
    have hza := CSE.Mem.args_two hzsz
    have hzcl := H.cl z zv hzA hzv (by rw [hzop]; decide)
    have hqA := hzcl zv.args[0]! (by rw [hza]; simp)
    have hm0A := hzcl zv.args[1]! (by rw [hza]; simp)
    obtain ⟨_, qv, -, hqv, -⟩ := H.val _ hqA
    obtain ⟨_, m0v, -, hm0v, -⟩ := H.val _ hm0A
    obtain ⟨zv2, yz, hzv2, hyz, hevz⟩ := H.val z hzA
    rw [hzv] at hzv2; cases hzv2
    obtain ⟨Q, M0, Z, hQw, rfl, hZ, rfl⟩ := zero_ok hzop hza hqv hm0v (hevz (by rw [hzop]; decide))
    rw [hM] at hyz
    have hMZ := (retype_mem_eq (Option.some.inj (Option.some.inj hyz)).symm).2
    subst hMZ
    have h1 := samePtr_reg H hT hid hqA hpA hce
    rw [hpv] at h1
    rw [h1] at hqv
    cases (Option.some.inj (Option.some.inj hqv))
    rw [hP] at hQw; cases hQw
    have := Pass.LoadFwd.read_write_self hZ
    rwa [Array.size_replicate, hzai] at this
  -- the anchor's source store and the stores below it
  have ha1 := CSE.Mem.args_three hsz1
  have hcl1 := H.cl m1 sv1 hm1A hsv1 (by rw [hop1]; decide)
  have hA0 := hcl1 sv1.args[0]! (by rw [ha1]; simp)
  have hA1 := hcl1 sv1.args[1]! (by rw [ha1]; simp)
  have hA2 := hcl1 sv1.args[2]! (by rw [ha1]; simp)
  obtain ⟨_, qv1, -, hqv1, -⟩ := H.val _ hA0
  obtain ⟨_, xv1, -, hxv1, -⟩ := H.val _ hA1
  obtain ⟨_, mv2, -, hmv2, -⟩ := H.val _ hA2
  obtain ⟨v1, y1, hv1, hy1, hev1⟩ := H.val m1 hm1A
  rw [hsv1] at hv1; cases hv1
  obtain ⟨Q1, M2, M1', hQ1, rfl, hw1, rfl⟩ :=
    store_ok hop1 ha1 hqv1 hxv1 hmv2 (hev1 (by rw [hop1]; decide))
  obtain ⟨hsop, htop, hsa, hta, haux, htype, hval, -, -, hszp, hqf, q, q', hq, hq', hqop, hqa,
    hqty, hce1, hq'op, hq'a, hq'ai, hq'ty, h0q, hle⟩ := moveStoreOK_spec hpair
  have ho : q.auxInt.toInt = ((q.auxInt.toInt.toNat : Nat) : Int) := (Int.toNat_of_nonneg h0q).symm
  have hqcA : A q.args[0]! := H.cl _ q hA0 hq (by rw [hqop]; decide) _
    (by rw [StructStore.args1 hqa]; simp)
  have hQe := offPtr_reg_of H hid hA0 hq hqop hqa ho hqty
    (samePtr_reg H hT hid hqcA hpA hce1) hpv hP hqv1 hQ1
  subst hQe
  rw [hid m1 sv1 hm1A hsv1, Proof.tys_of_value hsv1, Option.getD_some, hM1] at hy1
  obtain ⟨hty1, hM1'⟩ := retype_mem_eq (Option.some.inj (Option.some.inj hy1)).symm
  subst M1'
  change M2.write _ (encode (auxTy tabs sv1.aux) xv1) = some M1 at hw1
  obtain ⟨ws1, hr1, hin1, ⟨Mz, hMz, hzA⟩, htg⟩ := move_below (b := fv.block) (dst := d) (z' := z')
    (Dst := Dst) H hT hid hpA hpv hP hz fs1 ns sv1.args[2]! (lastArg gv) M2 hsc1 hgc
    (by simpa using hlen) (fun u hu v hv => hgid u (by simp [hu]) v hv) hzip1 hmv2 hA2
  have he : (encode (auxTy tabs sv1.aux) xv1).size = (auxTy tabs sv1.aux).size :=
    Sem.encode_size _ _
  have hle' : q.auxInt.toInt.toNat + (auxTy tabs sv1.aux).size ≤ fv.auxInt.toInt.toNat := by omega
  obtain ⟨ws, hws⟩ : ∃ ws, ws = ws1 ++ [(q.auxInt.toInt.toNat, encode (auxTy tabs sv1.aux) xv1)] :=
    ⟨_, rfl⟩
  have hW : M1.read P fv.auxInt.toInt.toNat =
      some (putAll (Array.replicate fv.auxInt.toInt.toNat (.b 0)) ws) := by
    rw [hws, putAll_snoc]
    exact read_write_putBytes hr1 hw1 (by rw [he]; exact hle')
  have hin : ∀ w ∈ ws, w.1 + w.2.size ≤ fv.auxInt.toInt.toNat := by
    intro w hw'
    rw [hws] at hw'
    rcases List.mem_append.1 hw' with hw' | hw'
    · exact hin1 w hw'
    · simp only [List.mem_singleton] at hw'; subst hw'
      show q.auxInt.toInt.toNat + (encode (auxTy tabs sv1.aux) xv1).size ≤ _
      rw [he]; exact hle'
  -- the `Move` read bytes the stores' bytes refine
  obtain ⟨R', hR', hRR⟩ := href.read hR
  rw [hW] at hR'; cases hR'
  -- the target's writes
  obtain ⟨Tz, hTz⟩ := StructStore.write_size_congr hMs (bs' := Array.replicate fv.auxInt.toInt.toNat (.b 0))
    (by rw [Array.size_replicate, hRs])
  obtain ⟨T, hWs, hT⟩ := writes_putBytes ws hTz fun w hw' => by
    rw [Array.size_replicate]; exact hin w hw'
  obtain ⟨T', hT', hMsT⟩ := (Mem.Refines.refl Mm).write hRR hMs
  rw [hT] at hT'; cases hT'
  rw [hws] at hWs
  obtain ⟨W1, hW1, hwT⟩ := writes_snoc hWs
  -- the fresh `OffPtr`s
  have hoffs : ∀ b ∈ x :: ns, ∀ sb, g.value? b = some sb → ∃ qv, g.value? sb.args[0]! = some qv ∧
      qv.id = sb.args[0]! ∧ qv.op = .OffPtr ∧ qv.args = #[d] ∧
      isPtrTy (tabs.ty qv.type) = true ∧ 0 ≤ qv.auxInt.toInt ∧
      (Dst.add (BitVec.ofNat 64 qv.auxInt.toInt.toNat)).inWindow = true ∧
      f.value? sb.args[0]! = none := by
    intro b hb sb hsb
    obtain ⟨a, hpa⟩ := zip_all_right hzip0 (by simpa using hlen) b hb
    cases hfa' : f.value? a with
    | none => simp only [hfa', hsb] at hpa; cases hpa
    | some sa =>
    simp only [hfa', hsb] at hpa
    obtain ⟨-, -, -, -, -, -, -, -, -, hszp', hqf', qa, qb, -, hqb, -, -, -, -, hqbop, hqba, hqbai,
      hqbty, h0a, hlea⟩ := moveStoreOK_spec hpa
    have hqbm : sb.args[0]! ∈ (x :: ns).filterMap fun b => (g.value? b).map (·.args[0]!) :=
      List.mem_filterMap.2 ⟨b, hb, by simp [hsb]⟩
    refine ⟨qb, hqb, hgid _ (by simp [hqbm]) qb hqb, hqbop, hqba, hqbty, by rw [hqbai]; exact h0a,
      ?_, hqf'⟩
    rw [hqbai]
    exact StructStore.inWindow_of_write hMs (by rw [hRs]; omega)
  obtain ⟨FrA, heA, hagA, hszA, hoffA, -⟩ :=
    eval_offs (g := g) H hdA hdv hD (x :: ns) hoffs S (fun _ _ => rfl) hsize
  -- the fresh `Zero`
  have hzty : tabs.ty zv.type = .mem := by
    have hza := CSE.Mem.args_two hzsz
    have hzcl := H.cl z zv hzA hzv (by rw [hzop]; decide)
    obtain ⟨_, qv, -, hqv, -⟩ := H.val _ (hzcl zv.args[0]! (by rw [hza]; simp))
    obtain ⟨_, m0v, -, hm0v, -⟩ := H.val _ (hzcl zv.args[1]! (by rw [hza]; simp))
    obtain ⟨zv2, yz, hzv2, hyz, hevz⟩ := H.val z hzA
    rw [hzv] at hzv2; cases hzv2
    obtain ⟨Q, M0, Z, -, rfl, -, rfl⟩ := zero_ok hzop hza hqv hm0v (hevz (by rw [hzop]; decide))
    rw [hid z zv hzA hzv, Proof.tys_of_value hzv, Option.getD_some, hMz] at hyz
    exact (retype_mem_eq (Option.some.inj (Option.some.inj hyz)).symm).1
  have hzvid : zv'.id = z' := hgid z' (by simp) zv' hzv'
  have hTz' : Mm.write Dst (Array.replicate zv'.auxInt.toInt.toNat (.b 0)) = some Tz := by
    rw [hz'ai]; exact hTz
  have hevz := zero_eval (env := env) (ctx := Ctx.make tabs g) (fr := FrA) hz'op hz'a
    (by rw [hagA d hdA]; exact hdv) hD (by rw [hagA m hmA]; exact hmv) hTz'
  rw [hzvid, Proof.tys_of_value hzv', Option.getD_some, hz'ty, hzty, retype_mem_mem] at hevz
  have hzlt : z' < FrA.regs.size := Nat.lt_of_lt_of_le (CheckFacts.lt_of_value? hzv') hszA
  have hagB : ∀ a, A a → (FrA.set z' (.mem Tz)).regs[a]? = S.regs[a]? := fun a ha => by
    have hne : z' ≠ a := by
      rintro rfl
      obtain ⟨_, _, hv, -⟩ := H.val z' ha
      rw [hfz'] at hv; cases hv
    rw [Proof.Frame.set_regs_ne hne, hagA a ha]
  have hoffB := hoffA.set_other hzv' (by rw [hz'op]; decide) (.mem Tz)
  -- the fresh stores below the anchor
  obtain ⟨FrC, heC, hrC, hagC, hszC, hoffC⟩ := htg Tz W1 hW1 (FrA.set z' (.mem Tz)) hagB
    (by simpa [Frame.set] using hszA) (fun b hb => hoffB b (List.mem_cons_of_mem _ hb))
    (Proof.Frame.set_regs_self hzlt) hnsf
  -- the anchor
  obtain ⟨yq, hyq, hyqw⟩ := hoffC _ hoffB x List.mem_cons_self gv q' hgv hq' hq'op
  rw [hq'ai] at hyqw
  have hga : gv.args = #[gv.args[0]!, sv1.args[1]!, lastArg gv] := by
    rw [lastArg_three hta, ← hval]; exact CSE.Mem.args_three hta
  have hev := store_eval (env := env) (ctx := Ctx.make tabs g) htop hga hyq hyqw
    (by rw [hagC _ hA1]; exact hxv1) hrC
    (by rw [show (Ctx.make tabs g).tabs = tabs from rfl, haux]; exact hwT)
  rw [hgid x (by simp) gv hgv, Proof.tys_of_value hgv, Option.getD_some] at hev
  have hxlt : x < FrC.regs.size := Nat.lt_of_lt_of_le (CheckFacts.lt_of_value? hgv) hszC
  refine ⟨FrC.set x ((Val.mem T).retype (tabs.ty gv.type)), ?_, fun _ => ⟨_, _, hyx,
    Proof.Frame.set_regs_self hxlt, ?_⟩⟩
  · rw [List.append_assoc, Proof.evalAll_append, heA]
    dsimp only
    rw [List.cons_append, Proof.evalAll_cons]
    simp only [Proof.stepV, show (Ctx.make tabs g).f = g from rfl, hzv', hevz]
    rw [Proof.evalAll_append, heC]
    dsimp only
    rw [Proof.evalAll_cons]
    simp only [Proof.stepV, show (Ctx.make tabs g).f = g from rfl, hgv, hev]
    rfl
  · rw [hid x fv hxA hfv, Proof.tys_of_value hfv, Option.getD_some, ← hty]
    exact retype_mono _ (.mem hMsT)
/-! ## Non-vacuity: a `Move` of a store over a zeroed temporary

`f`: `v4 = Zero [16] v3 v1` (`v3 = OffPtr [16] SP`), `v7 = Store {int64} (OffPtr [8] v3) v6 v4`,
`v8 = Move [16] SP v3 v7`; `g`: `v8 = Store {int64} v9 v6 v10` over the fresh
`v9 = OffPtr [8] SP` and `v10 = Zero [16] SP v7`. Nothing is dropped; `[v9, v10]` are fresh. -/

section Witness
open GoFV.Proof.CSE.Mem.Witness (tabs val)

private def mv (id : ID) (op : Op) (type : TypeRef) (auxInt : Int64) (aux : Option AuxRef)
    (args : Array ID) : Value :=
  { val id op type aux args with auxInt }

private def mf : Func :=
  { (default : Func) with
    valueTab := #[none, some (mv 1 .InitMem 2 0 none #[]), some (mv 2 .SP 1 0 none #[]),
      some (mv 3 .OffPtr 1 16 none #[2]), some (mv 4 .Zero 2 16 (some 2) #[3, 1]),
      some (mv 5 .OffPtr 1 8 none #[3]), some (mv 6 .Const64 0 0 none #[]),
      some (mv 7 .Store 2 0 (some 2) #[5, 6, 4]), some (mv 8 .Move 2 16 (some 2) #[2, 3, 7])] }

private def mg : Func :=
  { (default : Func) with
    valueTab := #[none, some (mv 1 .InitMem 2 0 none #[]), some (mv 2 .SP 1 0 none #[]),
      some (mv 3 .OffPtr 1 16 none #[2]), some (mv 4 .Zero 2 16 (some 2) #[3, 1]),
      some (mv 5 .OffPtr 1 8 none #[3]), some (mv 6 .Const64 0 0 none #[]),
      some (mv 7 .Store 2 0 (some 2) #[5, 6, 4]), some (mv 8 .Store 2 0 (some 2) #[9, 6, 10]),
      some (mv 9 .OffPtr 1 8 none #[2]), some (mv 10 .Zero 2 16 (some 2) #[2, 7])] }

theorem moveSeg_witness :
    moveSeg? tabs mf mg 8 (mv 8 .Move 2 16 (some 2) #[2, 3, 7]) (mv 8 .Store 2 0 (some 2) #[9, 6, 10]) =
      some ([], [9, 10]) := by
  decide +kernel

end Witness

end GoFV.Proof.Seg
