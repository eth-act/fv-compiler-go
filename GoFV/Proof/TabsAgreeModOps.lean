import GoFV.Proof.TabsAgreeModMem
import GoFV.Proof.Pass.DAECall

variable [GoFV.SSA.Sem.Addrs]

/-!
# Running in tables with extra frame temporaries: ops on related memories

The ops of `GoFV.Opt.tamMemOps` on argument lists `L ++ [w]` and `L ++ [w']` with related last
arguments (`VR X w w'`, memories equal up to the extra frame temporaries `X`) and source
arguments that avoid `X` evaluate to related results (`memOp_rel`): tuple ops, loads (their
pointers avoid `X`, so they read the same bytes: `EqX.load`), the memory roots (the same write
outside `X`: `EqX.write`), `NilCheck`, `PanicBounds`, and calls, whose contracts cannot tell
whether the blocks of `X` exist (`Env.TempOblivious`). The argument-shape lemmas that do not
depend on the relation are `dead auto elim`'s (`GoFV.Proof.DAE`).
-/

namespace GoFV.Proof.TabsMod

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DSE

variable {X : Blk → Bool}

theorem notX {b : Blk} (h : ¬ X b = true) : X b = false := by simpa using h

/-- The pointer a word avoiding `X` reads as is outside `X` (`DAE.asPtrWord_notU`). -/
theorem wordX (hX : TempX X) {a : Val} (ha : Val.Avoids (X · = true) a) {p : Ptr}
    (hp : a.asPtrWord = some p) : X p.blk = false :=
  notX (DAE.asPtrWord_notU (tempU_of hX) ha hp)

theorem VRL.snoc (L : List Val) {w w' : Val} (h : VR X w w') : VRL X (L ++ [w]) (L ++ [w']) :=
  VRL.append (VRL.refl L) (.cons h .nil)

/-! ## Pure ops on the last argument -/

theorem evalOp_pureOp' {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty} {argv : List Val}
    (hop : v.op = .Dereference ∨ v.op = .AtomicLoad8 ∨ v.op = .AtomicLoadAcq32 ∨
      v.op = .AtomicLoadAcq64 ∨ v.op = .SelectNAddr ∨ v.op = .MakeTuple) :
    evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) := by
  rcases hop with h | h | h | h | h | h <;> (simp only [evalOp, frameVal, h]; rfl)

theorem select_rel (i : Nat) (L : List Val) {w w' : Val} (h : VR X w w') :
    VR X (Tuple.select i (L ++ [w])) (Tuple.select i (L ++ [w'])) := by
  cases L with
  | cons x L =>
    rw [DAE.select_len i (by simp), DAE.select_len i (by simp)]; exact .refl _
  | nil =>
    cases h with
    | refl => exact .refl _
    | mem => exact .refl _
    | tuple h => exact h.getD i

theorem selectN_rel (k : Int64) (L : List Val) {w w' : Val} (h : VR X w w') :
    VR X (Tuple.selectN k (L ++ [w])) (Tuple.selectN k (L ++ [w'])) := by
  cases L with
  | cons x L =>
    rw [DAE.selectN_len k (by simp), DAE.selectN_len k (by simp)]; exact .refl _
  | nil =>
    cases h with
    | refl => exact .refl _
    | mem => exact .refl _
    | tuple h =>
      simp only [List.nil_append, Tuple.selectN]
      split
      · exact .refl _
      · exact h.getD _

theorem selectNAddr_eq (k : Int64) (L : List Val) {w w' : Val} (h : VR X w w') :
    Tuple.selectNAddr k (L ++ [w']) = Tuple.selectNAddr k (L ++ [w]) := by
  match L with
  | a :: L' =>
    have h1 : ∀ z, Tuple.selectNAddr k (a :: L' ++ [z]) = .poison := fun z => by
      obtain ⟨y, r, hy⟩ := DAE.snoc_cons L' z
      rw [List.cons_append, hy]
      cases a <;> rfl
    rw [h1, h1]
  | [] =>
    cases h with
    | refl => rfl
    | mem => rfl
    | tuple h =>
      simp only [List.nil_append, Tuple.selectNAddr]
      rcases h.getLast? with ⟨h1, h2⟩ | ⟨a, b, h1, h2, hab⟩
      · rw [h1, h2]
      · rw [h1, h2]
        cases hab with
        | refl => rfl
        | mem => rfl
        | tuple => rfl

theorem makeTuple_rel (L : List Val) {w w' : Val} (h : VR X w w') :
    VR X (Tuple.make (L ++ [w])) (Tuple.make (L ++ [w'])) := by
  match L with
  | [x] => exact .tuple (.cons (.refl x) (.cons h .nil))
  | [] => exact .refl _
  | a :: b :: L' =>
    have h1 : ∀ z, Tuple.make (a :: b :: L' ++ [z]) = .poison := fun z => by
      obtain ⟨y, r, hy⟩ := DAE.snoc_cons L' z
      rw [List.cons_append, List.cons_append, hy]
      rfl
    rw [h1, h1]; exact .refl _

theorem copy_rel (ty : Ty) (k : Int64) (ax : Option AuxRef) (L : List Val) {w w' : Val}
    (h : VR X w w') :
    VR X (evalPure .Copy ty k ax (L ++ [w])) (evalPure .Copy ty k ax (L ++ [w'])) := by
  cases L with
  | nil => exact h
  | cons x L => rw [DAE.copy_len _ _ _ (by simp), DAE.copy_len _ _ _ (by simp)]; exact .refl _

/-! ## Loads -/

theorem loadOp_eq (hX : TempX X) (t : Ty) (L : List Val) {w w' : Val} (h : VR X w w')
    (hav : ∀ a ∈ L, Val.Avoids (X · = true) a) : loadOp t (L ++ [w']) = loadOp t (L ++ [w]) := by
  match L, hav with
  | [x], hav =>
    cases h with
    | refl => rfl
    | tuple => cases x <;> rfl
    | mem hm =>
      simp only [List.cons_append, List.nil_append, loadOp]
      cases hp : x.asPtrWord with
      | none => rfl
      | some p => exact EqX.load hm t p (wordX hX (hav _ List.mem_cons_self) hp)
  | [], _ => rw [DAE.loadOp_len t (by simp), DAE.loadOp_len t (by simp)]
  | _ :: _ :: _, _ => rw [DAE.loadOp_len t (by simp), DAE.loadOp_len t (by simp)]

theorem atomicLoad_rel (hX : TempX X) (t : Ty) (L : List Val) {w w' : Val} (h : VR X w w')
    (hav : ∀ a ∈ L, Val.Avoids (X · = true) a) :
    VR X (atomicLoad t (L ++ [w])) (atomicLoad t (L ++ [w'])) := by
  match L, hav with
  | [x], hav =>
    cases h with
    | refl => exact .refl _
    | tuple => cases x <;> exact .refl _
    | mem hm =>
      simp only [List.cons_append, List.nil_append, atomicLoad]
      cases hp : x.asPtrWord with
      | none => exact .refl _
      | some p =>
        have hu : X p.blk = false := wordX hX (hav _ List.mem_cons_self) hp
        split
        · rename_i heq
          cases heq
          split
          · exact .tuple (.cons (.refl _) (.cons (.mem hm) .nil))
          · rw [EqX.load hm _ p hu]
            exact .tuple (.cons (.refl _) (.cons (.mem hm) .nil))
        · exact .refl _
  | [], _ => rw [DAE.atomicLoad_len t (by simp), DAE.atomicLoad_len t (by simp)]; exact .refl _
  | _ :: _ :: _, _ =>
    rw [DAE.atomicLoad_len t (by simp), DAE.atomicLoad_len t (by simp)]; exact .refl _

theorem memEq_eq (hX : TempX X) (L : List Val) {w w' : Val} (h : VR X w w')
    (hav : ∀ a ∈ L, Val.Avoids (X · = true) a) : memEq (L ++ [w']) = memEq (L ++ [w]) := by
  match L, hav with
  | [a, b, c], hav =>
    simp only [List.cons_append, List.nil_append]
    cases h with
    | refl => rfl
    | tuple => rw [DAE.memEq_tuple, DAE.memEq_tuple]
    | mem hm =>
      rcases c with ⟨w, n⟩ | _ | _ | _ | _ | _ | _ | _ | _ <;> try rfl
      simp only [memEq]
      cases hp : a.asPtrWord with
      | none => rfl
      | some p =>
      cases hq : b.asPtrWord with
      | none => rfl
      | some q =>
      have hp' : X p.blk = false := wordX hX (hav _ List.mem_cons_self) hp
      have hq' : X q.blk = false :=
        wordX hX (hav _ (List.mem_cons_of_mem _ List.mem_cons_self)) hq
      simp only [EqX.read hm _ _ hp', EqX.read hm _ _ hq']
  | [], _ => rw [DAE.memEq_len (by simp), DAE.memEq_len (by simp)]
  | [_], _ => rw [DAE.memEq_len (by simp), DAE.memEq_len (by simp)]
  | [_, _], _ => rw [DAE.memEq_len (by simp), DAE.memEq_len (by simp)]
  | _ :: _ :: _ :: _ :: _, _ => rw [DAE.memEq_len (by simp), DAE.memEq_len (by simp)]

/-! ## The memory roots -/

/-- **A `Store`/`Zero`/`Move`** on related memories. -/
theorem write_rel (hX : TempX X) {ctx : Ctx} {v : Value}
    (hop : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move)
    {L : List Val} {w w' : Val} (hw : VR X w w') (hav : ∀ a ∈ L, Val.Avoids (X · = true) a)
    {y : Val} (h : memRoot ctx v (L ++ [w]) = .ok y) :
    ∃ y', memRoot ctx v (L ++ [w']) = .ok y' ∧ VR X y y' := by
  obtain ⟨a, p, L0, M, bs, M1, he, hap, hwr, rfl, -, htgt⟩ := DAE.write_spec hop h
  obtain ⟨rfl, rfl⟩ := DAE.snoc_cons_eq he
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  have hp : X p.blk = false := wordX hX (hav _ List.mem_cons_self) hap
  obtain ⟨M1', hw', hm1⟩ := EqX.write hm hp hwr
  refine ⟨_, ?_, .mem hm1⟩
  rw [List.cons_append]
  refine htgt M' M1' (fun b s _ hL hs => ?_) hw'
  subst hL
  exact EqX.read hm s _ (wordX hX (hav b (by simp)) hs)

/-- **`VarLive`, `KeepAlive`** pass their memory through. -/
theorem varLive_rel {ctx : Ctx} {v : Value} (hop : v.op = .VarLive ∨ v.op = .KeepAlive)
    {L : List Val} {w w' : Val} (hw : VR X w w') {y : Val} (h : memRoot ctx v (L ++ [w]) = .ok y) :
    ∃ y', memRoot ctx v (L ++ [w']) = .ok y' ∧ VR X y y' := by
  obtain ⟨L0, M, he, rfl, htgt⟩ := DAE.varLive_spec hop h
  obtain ⟨rfl, rfl⟩ := DAE.snoc_inj he
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  exact ⟨_, htgt M', .mem hm⟩

/-- **`VarDef`** poisons the same block on both sides. -/
theorem varDef_rel {ctx : Ctx} {v : Value} (hop : v.op = .VarDef) {L : List Val} {w w' : Val}
    (hw : VR X w w') {y : Val} (h : memRoot ctx v (L ++ [w]) = .ok y) :
    ∃ y', memRoot ctx v (L ++ [w']) = .ok y' ∧ VR X y y' := by
  obtain ⟨M, n, he, hax, rfl, htgt⟩ := DSE.varDef_shape hop h
  obtain ⟨rfl, rfl⟩ := DAE.snoc_inj (L' := []) he
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  exact ⟨_, htgt M', .mem (varDefMem_rel (R := EqX X) hm (EqX.poison hm _))⟩

/-- **`NilCheck`** on related memories. -/
theorem nilCheck_rel {ctx : Ctx} {v : Value} (hop : v.op = .NilCheck) {L : List Val} {w w' : Val}
    (hw : VR X w w') :
    (∀ y, memRoot ctx v (L ++ [w]) = .ok y → memRoot ctx v (L ++ [w']) = .ok y) ∧
    (∀ e m, memRoot ctx v (L ++ [w]) = .panic e m →
      ∃ m', memRoot ctx v (L ++ [w']) = .panic e m' ∧ EqX X m m') := by
  constructor
  · intro y h
    obtain ⟨M, he, ht⟩ := DAE.nilCheck_ok hop h
    obtain ⟨rfl, rfl⟩ := DAE.snoc_inj (L' := [y]) he
    obtain ⟨M', rfl, -⟩ := VR.mem_inv hw
    exact ht M'
  · intro e m h
    obtain ⟨x, he, ht⟩ := DAE.nilCheck_panic hop h
    obtain ⟨rfl, rfl⟩ := DAE.snoc_inj (L' := [x]) he
    obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
    exact ⟨M', ht M', hm⟩

/-- **`PanicBounds`** panics alike on related memories. -/
theorem panicBounds_rel {k : Int64} {L : List Val} {w w' : Val} (hw : VR X w w') {e : Panic}
    {m : Mem} (h : panicBounds k (L ++ [w]) = .panic e m) :
    ∃ m', panicBounds k (L ++ [w']) = .panic e m' ∧ EqX X m m' := by
  obtain ⟨L0, he, ht⟩ := DAE.panicBounds_panic h
  obtain ⟨rfl, rfl⟩ := DAE.snoc_inj he
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  exact ⟨M', ht M', hm⟩

/-! ## Calls -/

theorem outargs_X (hX : TempX X) (a : Nat) : X (.outargs a) = false := by
  cases h : X (.outargs a)
  · rfl
  · obtain ⟨n, hn⟩ := hX _ h; cases hn

/-- `decodeArgs` reads only the outgoing-arguments area. -/
theorem decodeArgs_eqX (hX : TempX X) (tabs : Tables) (act : Nat) {m m' : Mem}
    (hm : EqX X m m') : ∀ (ps : List ABIParam) (pieces : List Val),
      decodeArgs tabs act m' ps pieces = decodeArgs tabs act m ps pieces
  | [], [] => rfl
  | [], _ :: _ => rfl
  | p :: ps, pieces => by
    unfold decodeArgs
    have hr : ∀ o n, m'.read ⟨.outargs act, o⟩ n = m.read ⟨.outargs act, o⟩ n :=
      fun o n => EqX.read hm ⟨.outargs act, o⟩ n (outargs_X hX act)
    simp only [hr, decodeArgs_eqX hX tabs act hm ps]

/-- `encodeResults` writes the same bytes into the outgoing area on both sides; the source's
memory and pieces avoid `X`. -/
theorem encodeResults_eqX (hX : TempX X) (tabs : Tables) (act : Nat) :
    ∀ (ps : List ABIParam) (rs : List Val) {m m' : Mem} {r : List Val × Mem},
      EqX X m m' → encodeResults tabs act ps rs m = some r →
      ∃ m1', encodeResults tabs act ps rs m' = some (r.1, m1') ∧ EqX X r.2 m1' ∧
        ((∀ x ∈ rs, Val.Avoids (X · = true) x) → m.Avoids (X · = true) →
          r.2.Avoids (X · = true) ∧ ∀ p ∈ r.1, Val.Avoids (X · = true) p)
  | [], [], m, m', r, hm, he => by
    simp only [encodeResults] at he; cases he
    exact ⟨m', rfl, hm, fun _ h => ⟨h, by simp⟩⟩
  | [], _ :: _, _, _, _, _, he => by simp [encodeResults] at he
  | _ :: _, [], _, _, _, _, he => by simp [encodeResults] at he
  | p :: ps, x :: xs, m, m', r, hm, he => by
    unfold encodeResults at he ⊢
    dsimp only at he ⊢
    split
    · next hreg =>
      rw [ite_eq_left_of_eq_true _ _ (eq_true hreg)] at he
      cases hw : m.write ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (encode (tabs.ty p.type) x) with
      | none => rw [hw] at he; cases he
      | some m1 =>
        rw [hw] at he
        obtain ⟨m1', hw', hm1⟩ := EqX.write hm (outargs_X hX act) hw
        rw [hw']
        obtain ⟨m2', h1, h2, h3⟩ := encodeResults_eqX hX tabs act ps xs hm1 he
        refine ⟨m2', h1, h2, fun hx hmA => h3 (fun y hy => hx y (List.mem_cons_of_mem _ hy))
          (DAE.memAvoids_write hmA hw fun _ => DAE.encode_avoids _ (hx x List.mem_cons_self))⟩
    · next hreg =>
      rw [ite_eq_right_of_eq_false _ _ (eq_false hreg)] at he
      cases hn : encodeResults tabs act ps xs m with
      | none => simp [hn, bind, Option.bind] at he
      | some q =>
        simp only [hn, bind, Option.bind, pure] at he
        cases he
        obtain ⟨m1', h1, h2, h3⟩ := encodeResults_eqX hX tabs act ps xs hm hn
        refine ⟨m1', by simp [h1, bind, Option.bind, pure], h2, fun hx hmA => ?_⟩
        obtain ⟨h4, h5⟩ := h3 (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hmA
        refine ⟨h4, fun y hy => ?_⟩
        rcases List.mem_append.1 hy with hy | hy
        · exact DAE.toPieces_avoids (tempU_of hX) _ (hx x List.mem_cons_self) y hy
        · exact h5 y hy

/-- Related call results: a returning source's result avoids `X` and the target returns a
related one; a panicking source's panic value and memory avoid `X`, and its target panics alike
with a related memory. -/
def CallRel (X : Blk → Bool) (r r' : Res Val) : Prop :=
  (∀ y, r = .ok y → Val.Avoids (X · = true) y ∧ ∃ y', r' = .ok y' ∧ VR X y y') ∧
    (∀ e m, r = .panic e m →
      e.Avoids (X · = true) ∧ m.Avoids (X · = true) ∧ ∃ m', r' = .panic e m' ∧ EqX X m m')

theorem callRel_stuck (msg : String) (r' : Res Val) : CallRel X (.stuck msg) r' :=
  ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

/-- Filtering the allocations by a block predicate commutes with erasing `X`. -/
theorem EqX.filter {m m' : Mem} (h : EqX X m m') (F : Blk × Alloc → Bool) :
    EqX X { m with blocks := m.blocks.filter F } { m' with blocks := m'.blocks.filter F } := by
  have hb : (m.blocks.toList.filter fun e => !X e.1) = m'.blocks.toList.filter fun e => !X e.1 := by
    rw [← erase_toList, ← erase_toList, h]
  have h1 : m.nextHeap = m'.nextHeap := EqX.nextHeap h
  have h2 : m.nextAct = m'.nextAct := EqX.nextAct h
  refine mem_ext ?_ h1 h2
  simp only [erase_toList, Array.toList_filter]
  have key : ∀ l : List (Blk × Alloc),
      (l.filter F).filter (fun e => !X e.1) = (l.filter fun e => !X e.1).filter F := by
    intro l; simp only [List.filter_filter, Bool.and_comm]
  rw [key, key, hb]

/-- Equality once the blocks `X` are erased is a memory relation the panic machinery keeps
(`DeferRel.MemRel`). -/
theorem memRel_eqX : DeferRel.MemRel (X · = true) (EqX X) where
  refl := EqX.refl X
  find h b hu := EqX.find h (notX hu)
  set h b a _ := EqX.set h b a
  write h hu hw := EqX.write h (notX hu) hw
  poison h b := EqX.poison h b
  filter h F _ := EqX.filter h F
  nextAct h := (EqX.nextAct h).symm

/-- The environment's contracts respect `X` and `EqX X`. -/
theorem respects_of_tempOblivious {env : Env} (hE : env.TempOblivious) (hX : TempX X) :
    ∀ name c, env.extern name = some c → DeferRel.Respects (X · = true) (EqX X) c :=
  fun name c hc => DeferRel.respects_of_tempOblivious (hE name c hc) (tempU_of hX)

/-- **The runtime entry points of a call from activation `act` cannot tell whether unreachable
frame temporaries exist** when the environment's contracts cannot. -/
theorem _root_.GoFV.SSA.Sem.Env.TempOblivious.atAct {env : Env} (h : env.TempOblivious)
    (act : Nat) : (env.atAct act).TempOblivious := fun name c hc =>
  DeferRel.tempOblivious_of_respects fun X hX =>
    DeferRel.atAct_respects memRel_eqX hX
      (fun n c' hc' => DeferRel.respects_of_tempOblivious (h n c' hc') hX) act name c hc

/-- **A call on related arguments.** -/
theorem callOp_rel {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx} {v : Value}
    {L : List Val} {w w' : Val} (hw : VR X w w') (hav : ∀ a ∈ L ++ [w], Val.Avoids (X · = true) a) :
    CallRel X (callOp env ctx v (L ++ [w])) (callOp env ctx v (L ++ [w'])) := by
  have hU := tempU_of hX
  rcases DAE.callTarget_snoc ctx v L with ⟨callee?, clo, R, hclo, hR, hT⟩ | hT
  rotate_left
  · obtain ⟨msg, h⟩ := DAE.callOp_rest_nil (env := env) (hT w)
    rw [h]; (try dsimp only); exact callRel_stuck _ _
  unfold callOp
  rw [hT w, hT w']
  dsimp only
  simp only [List.getLast?_concat, List.dropLast_concat]
  have hwA : Val.Avoids (X · = true) w := hav w (by simp)
  have hLA : ∀ a ∈ L, Val.Avoids (X · = true) a := fun a ha => hav a (by simp [ha])
  rcases Classical.em (∃ M, w = .mem M) with ⟨M, rfl⟩ | hwm
  rotate_left
  · have : ∀ M, w ≠ .mem M := fun M h => hwm ⟨M, h⟩
    cases w <;> first | exact absurd rfl (this _) | (try dsimp only); exact callRel_stuck _ _
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  dsimp only [bind, Res.bind]
  have hMA : M.Avoids (X · = true) := hwA
  have hRA : ∀ a ∈ R, Val.Avoids (X · = true) a := fun a ha => hLA a (hR a ha)
  have hcloA : ∀ y ∈ clo, Val.Avoids (X · = true) y := fun y hy => hLA y (hclo y hy)
  rw [decodeArgs_eqX hX _ _ hm]
  -- the same arguments on both sides, avoiding `U`
  split
  · simp only [Res.ofOption]
    split
    rotate_left
    · rename_i hd; exfalso; split at hd <;> cases hd
    · (try dsimp only); exact callRel_stuck _ _
    rename_i args hd
    have hargs : ∀ a ∈ args, Val.Avoids (X · = true) a := by
      split at hd
      · rename_i hdec; cases hd; exact DAE.decodeArgs_avoids hU _ _ hMA _ hRA hdec
      · cases hd
    rw [hd]
    try dsimp only
    try dsimp only
    split
    · (try dsimp only); exact callRel_stuck _ _
    rw [EqX.outargsOK hX hm]
    split
    · (try dsimp only); exact callRel_stuck _ _
    split
    · refine ⟨fun _ h => (nomatch h), fun e m h => ?_⟩
      cases h
      exact ⟨trivial, DAE.memAvoids_poisonBelow hMA _ _, _, rfl, EqX.poisonBelow hm _ _⟩
    cases callee? with
    | none => (try dsimp only); exact callRel_stuck _ _
    | some callee =>
    simp only [Res.ofOption]
    try dsimp only
    cases hx : (env.atAct ctx.act).extern callee with
    | none => (try dsimp only); exact callRel_stuck _ _
    | some c =>
    try dsimp only
    generalize callFrame ctx.tabs v.aux _ _ = F
    have hc := DeferRel.atAct_respects memRel_eqX hU (respects_of_tempOblivious hE hX) ctx.act
      callee c hx args clo (M.poisonBelow (.outargs ctx.act) F) (M'.poisonBelow (.outargs ctx.act) F)
      hargs hcloA (DAE.memAvoids_poisonBelow hMA _ _) (EqX.poisonBelow hm _ _)
    revert hc
    generalize c args clo (M.poisonBelow (.outargs ctx.act) F) = o
    generalize c args clo (M'.poisonBelow (.outargs ctx.act) F) = o'
    intro hc
    cases o with
    | stuck msg => (try dsimp only); exact callRel_stuck _ _
    | panicked e r =>
      cases o' with
      | panicked e' r' =>
        obtain ⟨rfl, heA, hrA, hrr⟩ := hc
        exact ⟨fun _ h => (nomatch h), fun e1 m1 h => by cases h; exact ⟨heA, hrA, r', rfl, hrr⟩⟩
      | returned _ _ => exact (hc : False).elim
      | stuck _ => exact (hc : False).elim
    | returned rs r =>
      cases o' with
      | returned rs' r' =>
        obtain ⟨rfl, hrsA0, hrA, hrr⟩ := hc
        try dsimp only
        try simp only [Res.ofOption]
        split
        rotate_left
        · rename_i hd; exfalso; split at hd <;> cases hd
        · (try dsimp only); exact callRel_stuck _ _
        rename_i x he
        split at he
        rotate_left
        · cases he
        rename_i hea
        cases he
        obtain ⟨m1', he', hm1, hA⟩ := encodeResults_eqX hX ctx.tabs ctx.act _ _ hrr hea
        obtain ⟨hA1, hA2⟩ := hA (DAE.retypeResults_avoids hU ctx.tabs _ hrsA0) hrA
        rw [he']
        try dsimp only
        refine ⟨fun y hy => ?_, fun _ _ h => ?_⟩
        · cases hy
          refine ⟨?_, _, rfl, .tuple (VRL.append (VRL.refl _)
            (.cons (.mem hm1) (.cons (.refl _) .nil)))⟩
          show Val.AvoidsList (X · = true) _
          rw [DAE.avoidsList_iff]
          intro a ha
          rcases List.mem_append.1 ha with ha | ha
          · exact hA2 a ha
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl
            · exact hA1
            · show Val.AvoidsList (X · = true) _
              rw [DAE.avoidsList_iff]
              intro a ha
              simp only [List.mem_map] at ha
              obtain ⟨p, -, rfl⟩ := ha
              split
              · exact DAE.outargs_notU hU _
              · trivial
        · cases h
      | panicked _ _ => exact (hc : False).elim
      | stuck _ => exact (hc : False).elim
  · simp only [pure]
    try dsimp only
    have hargs := DAE.retypeResults_avoids hU ctx.tabs (List.filter (fun x => !x.out)
      ((Option.map (fun x => x.params.toList) (callABI? ctx.tabs v.aux)).getD [])) hRA
    generalize retypeResults ctx.tabs (List.filter (fun x => !x.out)
      ((Option.map (fun x => x.params.toList) (callABI? ctx.tabs v.aux)).getD [])) R = args
      at hargs ⊢
    split
    · (try dsimp only); exact callRel_stuck _ _
    rw [EqX.outargsOK hX hm]
    split
    · (try dsimp only); exact callRel_stuck _ _
    split
    · refine ⟨fun _ h => (nomatch h), fun e m h => ?_⟩
      cases h
      exact ⟨trivial, DAE.memAvoids_poisonBelow hMA _ _, _, rfl, EqX.poisonBelow hm _ _⟩
    cases callee? with
    | none => (try dsimp only); exact callRel_stuck _ _
    | some callee =>
    simp only [Res.ofOption]
    try dsimp only
    cases hx : (env.atAct ctx.act).extern callee with
    | none => (try dsimp only); exact callRel_stuck _ _
    | some c =>
    try dsimp only
    generalize callFrame ctx.tabs v.aux _ _ = F
    have hc := DeferRel.atAct_respects memRel_eqX hU (respects_of_tempOblivious hE hX) ctx.act
      callee c hx args clo (M.poisonBelow (.outargs ctx.act) F) (M'.poisonBelow (.outargs ctx.act) F)
      hargs hcloA (DAE.memAvoids_poisonBelow hMA _ _) (EqX.poisonBelow hm _ _)
    revert hc
    generalize c args clo (M.poisonBelow (.outargs ctx.act) F) = o
    generalize c args clo (M'.poisonBelow (.outargs ctx.act) F) = o'
    intro hc
    cases o with
    | stuck msg => (try dsimp only); exact callRel_stuck _ _
    | panicked e r =>
      cases o' with
      | panicked e' r' =>
        obtain ⟨rfl, heA, hrA, hrr⟩ := hc
        exact ⟨fun _ h => (nomatch h), fun e1 m1 h => by cases h; exact ⟨heA, hrA, r', rfl, hrr⟩⟩
      | returned _ _ => exact (hc : False).elim
      | stuck _ => exact (hc : False).elim
    | returned rs r =>
      cases o' with
      | returned rs' r' =>
        obtain ⟨rfl, hrsA0, hrA, hrr⟩ := hc
        try dsimp only
        try simp only [Res.ofOption]
        split
        rotate_left
        · rename_i hd; exfalso; split at hd <;> cases hd
        · (try dsimp only); exact callRel_stuck _ _
        rename_i x he
        split at he
        rotate_left
        · cases he
        rename_i hea
        cases he
        obtain ⟨m1', he', hm1, hA⟩ := encodeResults_eqX hX ctx.tabs ctx.act _ _ hrr hea
        obtain ⟨hA1, -⟩ := hA (DAE.retypeResults_avoids hU ctx.tabs _ hrsA0) hrA
        rw [he']
        try dsimp only
        refine ⟨fun y hy => ?_, fun _ _ h => ?_⟩
        · cases hy
          refine ⟨?_, _, rfl, .tuple (VRL.append (VRL.refl _)
            (.cons (.mem hm1) (.cons (.refl _) .nil)))⟩
          show Val.AvoidsList (X · = true) _
          rw [DAE.avoidsList_iff]
          intro a ha
          rcases List.mem_append.1 ha with ha | ha
          · exact DAE.retypeResults_avoids hU ctx.tabs _ hrsA0 a ha
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl
            · exact hA1
            · show Val.AvoidsList (X · = true) _
              rw [DAE.avoidsList_iff]
              intro a ha
              simp only [List.mem_map] at ha
              obtain ⟨p, -, rfl⟩ := ha
              split
              · exact DAE.outargs_notU hU _
              · trivial
        · cases h
      | panicked _ _ => exact (hc : False).elim
      | stuck _ => exact (hc : False).elim

end GoFV.Proof.TabsMod
