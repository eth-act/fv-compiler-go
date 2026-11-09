import GoFV.Proof.FinishMono
import GoFV.Proof.PureMono

variable [GoFV.SSA.Sem.Addrs]

/-!
# Calls are monotone in refinement

The pieces of `callOp` (phase P3): `callTarget` on refined arguments names the same callee
(unless the source's is unknown), a refined closure context and refined remaining arguments;
`ofPieces`/`toPieces`, `decodeArgs` and `encodeResults` map refined pieces and memories to refined
values and memories (a failing source carries no obligation).
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-- Optional values refined: both absent, or both present and refined. -/
inductive OptRefines : Option Val → Option Val → Prop where
  | none : OptRefines none none
  | some {a b : Val} : Refines a b → OptRefines (some a) (some b)

theorem RefinesList.cons_inv {a : Val} {as bs : List Val} (h : RefinesList (a :: as) bs) :
    ∃ b bs', bs = b :: bs' ∧ Refines a b ∧ RefinesList as bs' := by
  cases h with | cons h t => exact ⟨_, _, rfl, h, t⟩

theorem RefinesList.nil_inv {bs : List Val} (h : RefinesList [] bs) : bs = [] := by
  cases h; rfl

theorem RefinesList.append {as bs cs ds : List Val} (h : RefinesList as bs)
    (h' : RefinesList cs ds) : RefinesList (as ++ cs) (bs ++ ds) := by
  induction as generalizing bs with
  | nil => cases h; exact h'
  | cons a as ih => cases h with | cons h1 t => exact .cons h1 (ih t)

theorem RefinesList.dropLast : {as bs : List Val} → RefinesList as bs →
    RefinesList as.dropLast bs.dropLast
  | _, _, .nil => .nil
  | _, _, .cons _ .nil => .nil
  | _, _, .cons h (.cons h' t) => .cons h (RefinesList.dropLast (.cons h' t))

theorem RefinesList.map {α : Type} (f g : α → Val) (h : ∀ x, Refines (f x) (g x)) :
    (l : List α) → RefinesList (l.map f) (l.map g)
  | [] => .nil
  | x :: l => .cons (h x) (RefinesList.map f g h l)

/-- A poison-free source list is refined by a poison-free list. -/
theorem RefinesList.any_hasPoison {as bs : List Val} (h : RefinesList as bs)
    (hp : as.any Val.hasPoison = false) : bs.any Val.hasPoison = false := by
  rw [Val.any_hasPoison] at hp ⊢
  exact (h.noPoison hp).1

/-! ## Callee and closure -/

theorem codeTarget?_mono {a b : Val} (h : Refines a b) {s : String} (hs : codeTarget? a = some s) :
    codeTarget? b = some s := by
  cases h <;> simp_all [codeTarget?]

/-- `callTarget` on refined arguments. -/
theorem callTarget_mono (ctx : Ctx) (v : Value) {argv argv' : List Val} (h : RefinesList argv argv') :
    ((callTarget ctx v argv).1 = none ∨ (callTarget ctx v argv').1 = (callTarget ctx v argv).1) ∧
      OptRefines (callTarget ctx v argv).2.1 (callTarget ctx v argv').2.1 ∧
      RefinesList (callTarget ctx v argv).2.2 (callTarget ctx v argv').2.2 := by
  have hcode : ∀ {a b : Val}, Refines a b →
      (codeTarget? a = none ∨ codeTarget? b = codeTarget? a) := fun {a b} hab => by
    cases ha : codeTarget? a with
    | none => exact .inl rfl
    | some s => exact .inr (codeTarget?_mono hab ha)
  by_cases hc : v.op = .ClosureLECall ∨ v.op = .ClosureCall
  · have key : ∀ l, callTarget ctx v l = match l with
        | a :: b :: r => (codeTarget? a, some b, r)
        | l => (v.aux.bind ctx.tabs.callee?, none, l) := by
      intro l; unfold callTarget
      rcases hc with hc | hc <;> rw [hc] <;> rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
    rw [key, key]
    rcases h with _ | ⟨h1, _ | ⟨h2, t⟩⟩
    · exact ⟨.inr rfl, .none, .nil⟩
    · exact ⟨.inr rfl, .none, .cons h1 .nil⟩
    · exact ⟨hcode h1, .some h2, t⟩
  · by_cases hi : v.op = .InterLECall ∨ v.op = .InterCall
    · have key : ∀ l, callTarget ctx v l = match l with
          | a :: r => (codeTarget? a, none, r)
          | l => (v.aux.bind ctx.tabs.callee?, none, l) := by
        intro l; unfold callTarget
        rcases hi with hi | hi <;> rw [hi] <;> rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
      rw [key, key]
      rcases h with _ | ⟨h1, t⟩
      · exact ⟨.inr rfl, .none, .nil⟩
      · exact ⟨hcode h1, .none, t⟩
    · have key : ∀ l, callTarget ctx v l = (v.aux.bind ctx.tabs.callee?, none, l) := by
        intro l; unfold callTarget
        split <;> simp_all
      rw [key, key]
      exact ⟨.inr rfl, .none, h⟩

/-! ## Register pieces -/

theorem ofPieces_mono (t : Ty) {ps ps' : List Val} (h : RefinesList ps ps') :
    Refines (ofPieces t ps) (ofPieces t ps') :=
  decode_mono (putBytes_fold_mono h _ (BytesRefineA.refl _)) 0 t

theorem toPieces_mono (t : Ty) {v v' : Val} (h : Refines v v') :
    RefinesList (toPieces t v) (toPieces t v') := by
  unfold toPieces
  have hb := encode_mono t h
  generalize leaves t = ls
  induction ls with
  | nil => exact .nil
  | cons l ls ih => exact .cons (decode_mono hb _ _) ih

/-- `decodeArgs` on refined pieces and memories. -/
theorem decodeArgs_mono (tabs : Tables) (act : Nat) {m m' : Mem} (hm : Mem.Refines m m') :
    ∀ (ps : List ABIParam) {pieces pieces' : List Val} {args : List Val},
      RefinesList pieces pieces' → decodeArgs tabs act m ps pieces = some args →
      ∃ args', decodeArgs tabs act m' ps pieces' = some args' ∧ RefinesList args args'
  | [], _, _, _, .nil, hd => by
    simp only [decodeArgs] at hd; cases hd; exact ⟨[], rfl, .nil⟩
  | [], _, _, _, .cons _ _, hd => by simp [decodeArgs] at hd
  | p :: ps, pieces, pieces', args, hp, hd => by
    unfold decodeArgs at hd ⊢
    dsimp only at hd ⊢
    split
    · next he =>
      rw [if_pos he] at hd
      cases hr : m.read ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (tabs.ty p.type).size with
      | none => rw [hr] at hd; cases hd
      | some bs =>
        rw [hr] at hd
        obtain ⟨bs', hr', hb⟩ := hm.read hr
        rw [hr']
        cases hn : decodeArgs tabs act m ps pieces with
        | none => simp [hn, bind, Option.bind] at hd
        | some r =>
          simp only [hn, bind, Option.bind, pure] at hd
          cases hd
          obtain ⟨r', hn', hrr⟩ := decodeArgs_mono tabs act hm ps hp hn
          refine ⟨_, by simp [hn', bind, Option.bind, pure], .cons (decode_mono hb 0 _) hrr⟩
    · next he =>
      rw [if_neg he] at hd
      rw [← hp.length_eq]
      split
      · next hl => rw [if_pos hl] at hd; cases hd
      · next hl =>
        rw [if_neg hl] at hd
        cases hn : decodeArgs tabs act m ps (pieces.drop p.regs.size) with
        | none => simp [hn, bind, Option.bind] at hd
        | some r =>
          simp only [hn, bind, Option.bind, pure] at hd
          cases hd
          obtain ⟨r', hn', hrr⟩ := decodeArgs_mono tabs act hm ps (hp.drop _) hn
          refine ⟨_, by simp [hn', bind, Option.bind, pure],
            .cons (ofPieces_mono _ (hp.take _)) hrr⟩

/-- `retypeResults` on refined results. -/
theorem retypeResults_mono (tabs : Tables) :
    ∀ (ps : List ABIParam) {rs rs' : List Val}, RefinesList rs rs' →
      RefinesList (retypeResults tabs ps rs) (retypeResults tabs ps rs')
  | [], _, _, h => h
  | _ :: _, _, _, .nil => .nil
  | p :: ps, _, _, .cons h t => .cons (retype_mono _ h) (retypeResults_mono tabs ps t)

/-- `encodeResults` on refined results and memories. -/
theorem encodeResults_mono (tabs : Tables) (act : Nat) :
    ∀ (ps : List ABIParam) {rs rs' : List Val} {m m' : Mem} {r : List Val × Mem},
      RefinesList rs rs' → Mem.Refines m m' → encodeResults tabs act ps rs m = some r →
      ∃ r', encodeResults tabs act ps rs' m' = some r' ∧ RefinesList r.1 r'.1 ∧
        Mem.Refines r.2 r'.2
  | [], _, _, _, _, _, .nil, hm, he => by
    simp only [encodeResults] at he; cases he; exact ⟨_, rfl, .nil, hm⟩
  | [], _, _, _, _, _, .cons _ _, _, he => by simp [encodeResults] at he
  | _ :: _, _, _, _, _, _, .nil, _, he => by simp [encodeResults] at he
  | p :: ps, _, _, m, m', r, .cons (a := x) (b := x') (as := xs) (bs := xs') hx hrs, hm, he => by
    unfold encodeResults at he ⊢
    dsimp only at he ⊢
    split
    · next hreg =>
      rw [if_pos hreg] at he
      cases hw : m.write ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (encode (tabs.ty p.type) x) with
      | none => rw [hw] at he; cases he
      | some m1 =>
        rw [hw] at he
        obtain ⟨m1', hw', hm1⟩ := hm.write (encode_mono _ hx) hw
        rw [hw']
        exact encodeResults_mono tabs act ps hrs hm1 he
    · next hreg =>
      rw [if_neg hreg] at he
      cases hn : encodeResults tabs act ps xs m with
      | none => simp [hn, bind, Option.bind] at he
      | some q =>
        simp only [hn, bind, Option.bind, pure] at he
        cases he
        obtain ⟨q', hn', hq1, hq2⟩ := encodeResults_mono tabs act ps hrs hm hn
        exact ⟨(toPieces (tabs.ty p.type) x' ++ q'.1, q'.2), by simp [hn', bind, Option.bind, pure],
          (toPieces_mono _ hx).append hq1, hq2⟩

end GoFV.SSA.Sem
