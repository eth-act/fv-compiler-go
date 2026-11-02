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
    simp only [Array.getElem?_extract]
    by_cases hj : j < n
    · rw [if_pos (by simp only [CSE.Mem.foldl_set_size]; omega), if_pos (by omega),
        foldl_set_getElem? _ _ _ _ (Nat.le_refl _) (by omega)]
      by_cases hj' : o ≤ j ∧ j < o + E.size
      · rw [if_pos ⟨by omega, by omega⟩, if_pos hj']; congr 1; omega
      · rw [if_neg (by omega), if_neg hj']
        simp only [Array.getElem?_extract, if_pos (show P.off.toNat + j < a.data.size by omega),
          if_pos hj]
    · rw [if_neg (by simp only [CSE.Mem.foldl_set_size]; omega), if_neg (by omega)]
      by_cases hj' : o ≤ j ∧ j < o + E.size
      · omega
      · rw [if_neg hj']
        simp only [Array.getElem?_extract, if_neg hj]

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
  have hv : v.args = #[d, p, m] := by rw [← Array.toArray_toList v.args, ha]
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
  unfold memRoot at ho'
  rw [hop] at ho'
  split at ho' <;> try (rename_i h1 _; cases h1; done)
  · rename_i M _
    split at ho'
    · cases ho'; exact ⟨M, _, rfl, rfl⟩
    · cases ho'
  all_goals (split at ho' <;> cases ho')

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
    hai, Ptr.step?, if_pos hin]

/-! ## The validator's facts -/

theorem moveStoreOK_spec {tabs : Tables} {f g : Func} {p dst : ID} {n : Int64} {b : ID}
    {sa sb : Value} (h : moveStoreOK tabs f g p dst n b sa sb = true) :
    sa.op = .Store ∧ sb.op = .Store ∧ sa.args.size = 3 ∧ sb.args.size = 3 ∧ sb.aux = sa.aux ∧
      sb.type = sa.type ∧ sb.args[1]! = sa.args[1]! ∧ sa.block = b ∧ sb.block = b ∧
      0 < (auxTy tabs sa.aux).size ∧ f.value? sb.args[0]! = none ∧
      ∃ q q', f.value? sa.args[0]! = some q ∧ g.value? sb.args[0]! = some q' ∧
        q.op = .OffPtr ∧ q.args.size = 1 ∧ isPtrTy (tabs.ty q.type) = true ∧
        copyEnd tabs f.valueTab f.valueTab.size q.args[0]! =
          copyEnd tabs f.valueTab f.valueTab.size p ∧
        q'.op = .OffPtr ∧ q'.args = #[dst] ∧ q'.auxInt = q.auxInt ∧
        isPtrTy (tabs.ty q'.type) = true ∧ 0 ≤ q.auxInt.toInt ∧
        q.auxInt.toInt + (auxTy tabs sa.aux).size ≤ n.toInt := by
  unfold moveStoreOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  split at h13
  · rename_i q q' hq hq'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h13
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩, k11⟩ := h13
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, q, q', hq, hq', k1, k2, k3, k4, k5, k6, k7,
      k8, k9, k10⟩
  · cases h13

/-! ## The chains -/

/-- `gs` are values of `g` from `t` down their last arguments, over `z'`. -/
def GChain (g : Func) : ID → List ID → ID → Prop
  | t, [], z' => t = z'
  | t, u :: us, z' => u = t ∧ ∃ uv, g.value? t = some uv ∧ GChain g (lastArg uv) us z'

theorem fchain_gchain {f g : Func} : ∀ {t m0 z' : ID} {ns : List ID},
    FChain f g t (ns ++ [z']) m0 → GChain g t ns z'
  | _, _, _, [], h => by obtain ⟨h1, -⟩ := h; exact h1.symm
  | _, _, _, _ :: _, ⟨h1, -, uv, huv, h⟩ => ⟨h1, uv, huv, fchain_gchain h⟩

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
theorem zip_all_right {α : Type} {P : ID × ID → Bool} : ∀ {fs gs : List ID},
    (fs.zip gs).all P = true → fs.length = gs.length → ∀ b ∈ gs, ∃ a, P (a, b) = true
  | [], [], _, _, b, hb => absurd hb List.not_mem_nil
  | a :: fs, c :: gs, h, hl, b, hb => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, h.1⟩
    · exact zip_all_right h.2 (by simpa using hl) b hb
  | [], _ :: _, _, hl, _, _ => by cases hl
  | _ :: _, [], _, hl, _, _ => by cases hl

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
          exact h5 [b'] this b' List.mem_cons_self sb' qv hb hqv hqop'
        · exact h4 b' hb'

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
        (∀ w ∈ ws, w.1 + w.2.size ≤ n.toInt.toNat) ∧ (∃ Mz, S.regs[z]? = some (some (.mem Mz))) ∧
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
    refine ⟨[], hz M hM hA, by simp, ⟨M, hM⟩, fun Tz T hW Fr hag hsz _ hz' _ => ?_⟩
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
    have ho : q.auxInt.toInt = ((q.auxInt.toInt.toNat : Nat) : Int) := (Int.toNat_of_nonneg h0).symm
    have hQe := offPtr_reg H hT hid hA0 hpA hq hqop (by rw [hqa]) ho hqty hce hP hpv hqv hQ
    subst hQe
    rw [hid s sv hA hs, Proof.tys_of_value hs, Option.getD_some, hM] at hy
    obtain ⟨hty, rfl⟩ := retype_mem_eq (Option.some.inj (Option.some.inj hy)).symm
    obtain ⟨ws1, hr1, hin1, hMz, htg⟩ := move_below H hT hid hpA hP hpv hz fs1 gs1 sv.args[2]!
      (lastArg tv) M1 hsc1 hgc1 (by simpa using hlen)
      (fun u hu => hgid u (List.mem_cons_of_mem _ hu)) hzip1 hmv hA2
    have hsz : (encode (auxTy tabs sv.aux) xv).size + q.auxInt.toInt.toNat ≤ n.toInt.toNat := by
      rw [Sem.encode_size]; omega
    refine ⟨ws1 ++ [(q.auxInt.toInt.toNat, encode (auxTy tabs sv.aux) xv)], ?_, ?_, hMz, ?_⟩
    · rw [putAll_snoc]
      exact read_write_putBytes hr1 hw (by omega)
    · intro w hw'
      rcases List.mem_append.1 hw' with hw' | hw'
      · exact hin1 w hw'
      · simp only [List.mem_singleton] at hw'; subst hw'; simp only; omega
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
      (m1 = m ∨ ∃ mv, f.value? m = some mv ∧ mv.op = .VarDef ∧ mv.args = #[m1]) ∧
      FChain f g (lastArg gv) (ns ++ [z']) m ∧ storesF f (ns.length + 1) m1 = some (fs, z) ∧
      f.value? z = some zv ∧ g.value? z' = some zv' ∧ gv.op = .Store ∧ 0 ≤ fv.auxInt.toInt ∧
      zv.op = .Zero ∧ zv.args.size = 2 ∧ zv.auxInt = fv.auxInt ∧
      copyEnd tabs f.valueTab f.valueTab.size zv.args[0]! =
        copyEnd tabs f.valueTab f.valueTab.size p ∧
      zv'.op = .Zero ∧ zv'.args = #[d, m] ∧ zv'.auxInt = fv.auxInt ∧ zv'.type = zv.type ∧
      (fs.zip (x :: ns)).all (fun (a, b) => match f.value? a, g.value? b with
        | some sa, some sb => moveStoreOK tabs f g p d fv.auxInt fv.block sa sb
        | _, _ => false) = true ∧
      N = ((x :: ns).filterMap fun b => (g.value? b).map (·.args[0]!)) ++ z' :: ns.reverse := by
  unfold moveSeg? at h
  split at h
  case h_2 => cases h
  rename_i d p m hop hargs
  generalize hm1 : (match f.value? m with
    | some mv => if mv.op == .VarDef && mv.args.size == 1 then mv.args[0]! else m
    | none => m) = m1 at h
  have hm1' : m1 = m ∨ ∃ mv, f.value? m = some mv ∧ mv.op = .VarDef ∧ mv.args = #[m1] := by
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
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgop, hm0⟩, h0⟩, hzop⟩, hzsz⟩, hzai⟩, hce⟩, hz'op⟩, hz'a⟩, hz'ai⟩, hz'ty⟩,
    hzip⟩ := hc
  subst hm0
  obtain ⟨ns, rfl⟩ : ∃ ns, ns0 = ns ++ [z'] := ⟨_, (List.dropLast_append_getLast? hl).symm⟩
  have hfc' := freshChain_chain hfc
  simp only [List.dropLast_concat, List.reverse_append, List.reverse_singleton,
    List.singleton_append] at hzip ⊢
  refine ⟨rfl, hop, d, p, m, m1, ns, z', fs, z, zv, zv', hargs, hm1', hfc', ?_, hzv, hzv',
    hgop, h0, hzop, hzsz, hzai, hce, hz'op, hz'a, hz'ai, hz'ty, hzip, rfl⟩
  simpa using hsf

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
  have hfa' : fv.args = #[d, p, m] := by rw [← Array.toArray_toList fv.args, hfa]
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
  set nn := fv.auxInt.toInt.toNat with hnn
  have hRs : R.size = nn := DSE.read_size hR
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
  sorry
end GoFV.Proof.Seg
