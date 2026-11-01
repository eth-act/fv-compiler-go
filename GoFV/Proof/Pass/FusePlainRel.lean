import GoFV.Opt.Fuse.PlainCheck
import GoFV.Proof.Checked
import GoFV.Proof.Agree
import GoFV.Proof.WF

/-!
# fuseBlockPlain: what the step checker establishes

`PRel f g run b0 c`: the run `run` starts at `b0`, ends at `c`, and `Plain.relB f g run` holds
(`GoFV.Opt.Fuse.PlainCheck`). This module unfolds the checker into the facts the simulation
uses: the chain links (`link`), the later blocks (`later`), the reads of the run's values
(`reads`), the unchanged values (`value_same`) and blocks (`block_out`), and the fused block
(`merged`).
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain GoFV.Proof

/-- One checked plain fusion of the run `run` from `b0` to `c`. -/
structure PRel (f g : Func) (run : List ID) (b0 c : ID) : Prop where
  head : run.head? = some b0
  last : run.getLast? = some c
  rel : relB f g run = true

variable {f g : Func} {run : List ID} {b0 c : ID}

theorem valsOf_mem {f : Func} {b x : ID} :
    x ∈ (valsOf f b).toList ↔ ∃ B, f.block? b = some B ∧ x ∈ B.values := by
  unfold valsOf
  cases h : f.block? b with
  | none => simp
  | some B => simp

/-- The checker's conjuncts. -/
theorem PRel.parts (h : PRel f g run b0 c) :
    b0 ≠ c ∧ run.Nodup ∧ (∀ x ∈ run, x ∈ f.blocks) ∧ chainOK f run = true ∧
      (∀ y ∈ run.tail, laterOK f y = true) ∧ readsAllOK f run = true ∧ g.blocks = f.blocks ∧
      (g.entry == (if f.entry == b0 then c else f.entry)) = true ∧ g.ownAux = f.ownAux ∧
      g.valueTab.size = f.valueTab.size ∧
      (∀ x, x < f.valueTab.size → valueOK f g x = true) ∧
      (∀ bid ∈ f.blocks, bid ∈ run ∨ blockOK f g b0 c bid = true) ∧
      mergedOK f g run b0 c = true := by
  have hr := h.rel
  unfold relB at hr
  rw [h.head, h.last] at hr
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem, Array.contains_iff_mem, List.mem_range, Bool.or_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hne, hnd⟩, hin⟩, hch⟩, hlat⟩, hrd⟩, hbl⟩, hent⟩, hown⟩, hsz⟩, hval⟩,
    hblk⟩, hm⟩ := hr
  refine ⟨hne, hnd, hin, hch, hlat, hrd, by simpa using hbl, hent, by simpa using hown,
    by simpa using hsz, hval, fun bid hb => ?_, hm⟩
  have := (Array.all_eq_true'.1 hblk) bid hb
  rcases Bool.or_eq_true_iff.1 this with h' | h'
  · exact .inl (by simpa using h')
  · exact .inr h'

theorem PRel.entry (h : PRel f g run b0 c) :
    (f.entry = b0 → g.entry = c) ∧ (f.entry ≠ b0 → g.entry = f.entry) := by
  have he := h.parts.2.2.2.2.2.2.2.1
  constructor
  · intro hb; subst hb; simpa using he
  · intro hb; simpa [hb] using he

theorem PRel.run_cons (h : PRel f g run b0 c) : ∃ rest, run = b0 :: rest := by
  have hh := h.head
  cases run with
  | nil => cases hh
  | cons x rest => cases hh; exact ⟨rest, rfl⟩

theorem PRel.c_mem (h : PRel f g run b0 c) : c ∈ run := List.mem_of_getLast? h.last

theorem PRel.b0_mem (h : PRel f g run b0 c) : b0 ∈ run := List.mem_of_mem_head? h.head

/-- `c` is the last block: nothing follows it. -/
theorem PRel.c_last (h : PRel f g run b0 c) {pre suf : List ID} (hr : run = pre ++ c :: suf) :
    suf = [] := by
  have hl := h.last
  have hnd := h.parts.2.1
  rw [hr] at hl hnd
  cases suf with
  | nil => rfl
  | cons y suf =>
    exfalso
    rw [List.getLast?_append, List.getLast?_cons_cons,
      List.getLast?_eq_getLast (l := y :: suf) (List.cons_ne_nil _ _), Option.some_or] at hl
    have hcl : c ∈ y :: suf := by
      cases hl; exact List.getLast_mem _
    rw [List.nodup_append] at hnd
    exact (List.nodup_cons.1 hnd.2.1).1 hcl

/-! ## Chain links -/

theorem chainOK_spec {f : Func} : ∀ {run : List ID}, chainOK f run = true →
    ∀ pre x y suf, run = pre ++ x :: y :: suf → linkOK f x y = true
  | [], _, pre, x, y, suf, hr => by cases pre <;> cases hr
  | [_], _, pre, x, y, suf, hr => by
    rcases pre with _ | ⟨_, _ | _⟩ <;> simp at hr
  | a :: b :: rest, h, pre, x, y, suf, hr => by
    unfold chainOK at h
    rw [Bool.and_eq_true] at h
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hr
      obtain ⟨rfl, rfl, -⟩ := hr
      exact h.1
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at hr
      exact chainOK_spec h.2 pre x y suf hr.2

theorem linkOK_spec {f : Func} {x y : ID} (h : linkOK f x y = true) :
    ∃ X Y, f.block? x = some X ∧ f.block? y = some Y ∧ X.kind = .Plain ∧
      X.succs = #[⟨y, 0⟩] ∧ Y.preds = #[⟨x, 0⟩] := by
  unfold linkOK at h
  cases hX : f.block? x with
  | none => rw [hX] at h; cases h
  | some X =>
    cases hY : f.block? y with
    | none => rw [hX, hY] at h; cases h
    | some Y =>
      rw [hX, hY] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨X, Y, rfl, rfl, h.1.1, h.1.2, h.2⟩

/-- Consecutive blocks of the run. -/
theorem PRel.link (h : PRel f g run b0 c) {pre suf : List ID} {x y : ID}
    (hr : run = pre ++ x :: y :: suf) :
    ∃ X Y, f.block? x = some X ∧ f.block? y = some Y ∧ X.kind = .Plain ∧
      X.succs = #[⟨y, 0⟩] ∧ Y.preds = #[⟨x, 0⟩] :=
  linkOK_spec (chainOK_spec h.parts.2.2.2.1 pre x y suf hr)

/-! ## Later blocks and reads -/

theorem laterOK_spec {f : Func} {y : ID} (h : laterOK f y = true) :
    y ≠ f.entry ∧ ∀ x ∈ (valsOf f y).toList, ∃ v, f.value? x = some v ∧ v.op ≠ .Phi ∧
      v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg := by
  unfold laterOK at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Array.all_eq_true'] at h
  refine ⟨h.1, fun x hx => ?_⟩
  have := h.2 x (Array.mem_toList_iff.1 hx)
  cases hv : f.value? x with
  | none => rw [hv] at this; cases this
  | some v =>
    rw [hv] at this
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact ⟨v, rfl, this.1.1, this.1.2, this.2⟩

/-- A block after `b0`: not the entry, no `Phi`, no parameter read. -/
theorem PRel.later (h : PRel f g run b0 c) {pre suf : List ID} {y : ID}
    (hr : run = pre ++ y :: suf) (hpre : pre ≠ []) :
    y ≠ f.entry ∧ ∀ x ∈ (valsOf f y).toList, ∃ v, f.value? x = some v ∧ v.op ≠ .Phi ∧
      v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg := by
  obtain ⟨rest, hrest⟩ := h.run_cons
  refine laterOK_spec (h.parts.2.2.2.2.1 y ?_)
  rw [hrest] at hr
  cases pre with
  | nil => exact absurd rfl hpre
  | cons p pre =>
    simp only [List.cons_append, List.cons.injEq] at hr
    rw [hrest, List.tail_cons, hr.2]; simp

theorem readsAllOK_spec {f : Func} : ∀ {run : List ID}, readsAllOK f run = true →
    ∀ pre x suf, run = pre ++ x :: suf → readsOK f x suf = true
  | [], _, pre, x, suf, hr => by cases pre <;> cases hr
  | a :: rest, h, pre, x, suf, hr => by
    unfold readsAllOK at h
    rw [Bool.and_eq_true] at h
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact h.1
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at hr
      exact readsAllOK_spec h.2 pre x suf hr.2

/-- A non-`Phi` of a block of the run reads no value of a later block. -/
theorem PRel.reads (h : PRel f g run b0 c) {pre suf : List ID} {x : ID}
    (hr : run = pre ++ x :: suf) {v : ID} (hv : v ∈ (valsOf f x).toList) {fv : Value}
    (hfv : f.value? v = some fv) (hnp : fv.op ≠ .Phi) {a : ID} (ha : a ∈ fv.args) {y : ID}
    (hy : y ∈ suf) : a ∉ (valsOf f y).toList := by
  have hok := readsAllOK_spec h.parts.2.2.2.2.2.1 pre x suf hr
  unfold readsOK at hok
  rw [Array.all_eq_true'] at hok
  have := hok v (Array.mem_toList_iff.1 hv)
  rw [hfv] at this
  have h1 : (fv.op == .Phi) = false := by simpa using hnp
  simp only [h1, Bool.false_or, Array.all_eq_true'] at this
  have h2 := this a ha
  rw [List.all_eq_true] at h2
  have h3 := h2 y hy
  intro hm
  rw [Array.contains_iff_mem.2 (Array.mem_toList_iff.1 hm)] at h3
  cases h3

/-! ## Values and blocks -/

/-- Every value is unchanged in what the semantics reads. -/
theorem PRel.value_same (h : PRel f g run b0 c) (x : ID) :
    SemEq (f.value? x) (g.value? x) ∧
      ∀ fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧ gv.type = fv.type ∧
        gv.op = fv.op ∧ gv.args = fv.args := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hsz, hval, -⟩ := h.parts
  rcases Nat.lt_or_ge x f.valueTab.size with hx | hx
  · have hv := hval x hx
    unfold valueOK at hv
    cases hf : f.value? x with
    | none =>
      rw [hf] at hv
      cases hg : g.value? x with
      | none => exact ⟨trivial, fun _ h => nomatch h⟩
      | some _ => rw [hg] at hv; cases hv
    | some fv =>
      rw [hf] at hv
      cases hg : g.value? x with
      | none => rw [hg] at hv; cases hv
      | some gv =>
        rw [hg] at hv
        unfold sameV at hv
        simp only [Bool.and_eq_true, beq_iff_eq] at hv
        obtain ⟨⟨⟨⟨⟨hid, hty⟩, haux⟩, hai⟩, hop⟩, hargs⟩ := hv
        exact ⟨⟨hid, hop, haux, hai, hargs⟩, fun fv' h' => by
          cases h'; exact ⟨gv, rfl, hty, hop, hargs⟩⟩
  · have h1 : f.value? x = none := by simp [Func.value?, Array.getElem?_eq_none hx]
    have h2 : g.value? x = none := by
      simp [Func.value?, Array.getElem?_eq_none (show g.valueTab.size ≤ x by omega)]
    rw [h1, h2]
    exact ⟨trivial, fun _ h => nomatch h⟩

/-- A listed block outside the run is unchanged but for edges into `b0`. -/
theorem PRel.block_out (h : PRel f g run b0 c) {bid : ID} (hb : bid ∈ f.blocks)
    (hn : bid ∉ run) :
    ∃ fb gb, f.block? bid = some fb ∧ g.block? bid = some gb ∧ gb.id = fb.id ∧
      gb.values = fb.values ∧ gb.kind = fb.kind ∧ gb.controls = fb.controls ∧
      gb.succs = fb.succs.map (redirect b0 c) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hblk, -⟩ := h.parts
  rcases hblk bid hb with h' | h'
  · exact absurd h' hn
  · unfold blockOK at h'
    cases hf : f.block? bid with
    | none => rw [hf] at h'; cases h'
    | some fb =>
      cases hg : g.block? bid with
      | none => rw [hf, hg] at h'; cases h'
      | some gb =>
        rw [hf, hg] at h'
        simp only [Bool.and_eq_true, beq_iff_eq] at h'
        obtain ⟨⟨⟨⟨hid, hv⟩, hk⟩, hc⟩, hs⟩ := h'
        exact ⟨fb, gb, rfl, rfl, hid, hv, hk, hc, hs⟩

/-- The fused block `c` of `g`. -/
theorem PRel.merged (h : PRel f g run b0 c) :
    ∃ C C' oT, f.block? c = some C ∧ g.block? c = some C' ∧ C'.id = c ∧
      C'.values.toList = run.flatMap (fun x => (valsOf f x).toList) ∧ C'.kind = C.kind ∧
      C'.controls = C.controls ∧ C'.succs = C.succs.map (redirect b0 c) ∧
      (∀ x ∈ run, (schedOf f x).isSome) ∧ schedule g C' = some oT ∧
      oT.toList.filter (fun y => run.any (npAt f · y)) = npSeq f run := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hm⟩ := h.parts
  unfold mergedOK at hm
  cases hC : f.block? c with
  | none => rw [hC] at hm; cases hm
  | some C =>
    cases hC' : g.block? c with
    | none => rw [hC, hC'] at hm; cases hm
    | some C' =>
      rw [hC, hC'] at hm
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hm
      obtain ⟨⟨⟨⟨⟨⟨hid, hv⟩, hk⟩, hc⟩, hs⟩, hsch⟩, ho⟩ := hm
      cases hoT : schedule g C' with
      | none => rw [hoT] at ho; cases ho
      | some oT =>
        rw [hoT] at ho
        exact ⟨C, C', oT, rfl, rfl, hid, hv, hk, hc, hs, hsch, hoT, by simpa using ho⟩

end GoFV.Proof.FusePlain
