import GoFV.Proof.Pass.DAERoot

/-!
# dead auto elim: calls under frame-safe contracts

A call whose arguments before the memory are equal in source and target and whose memories are
equal outside the frame temporaries `U` (`EqOff`) decodes the same Go-typed arguments (stack
arguments come from the outgoing-arguments area, not in `U`), which avoid `U` when the source's
arguments and memory do; a frame-safe contract (`Env.FrameSafe`) then returns the same results
with memories equal outside `U` (or panics alike), and `encodeResults` writes the same bytes
into the outgoing area on both sides (`callOp_rel`). The source's result avoids `U`.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.DAE GoFV.Proof.DSE

variable {U : Blk → Prop}

/-! ## Register pieces, decoded arguments, encoded results -/

theorem ofPieces_avoids (hU : TempU U) (t : Ty) {ps : List Val} (h : ∀ p ∈ ps, Val.Avoids U p) :
    Val.Avoids U (ofPieces t ps) := by
  unfold ofPieces
  refine decode_avoids hU ?_ 0 t
  have key : ∀ (l : List ((Nat × Ty) × Val)) (buf : Array Byte), BAv U buf →
      (∀ e ∈ l, Val.Avoids U e.2) →
      BAv U (l.foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v)) buf) := by
    intro l
    induction l with
    | nil => intro buf hb _; exact hb
    | cons e l ih =>
      intro buf hb he
      obtain ⟨⟨o, lt⟩, v⟩ := e
      simp only [List.foldl_cons]
      exact ih _ (bav_putBytes hb (encode_avoids lt (he _ List.mem_cons_self)) o)
        fun e' he' => he e' (List.mem_cons_of_mem _ he')
  exact key _ _ (bav_replicate_poison _ _) fun e he => h _ (List.of_mem_zip he).2

theorem toPieces_avoids (hU : TempU U) (t : Ty) {v : Val} (h : Val.Avoids U v) :
    ∀ p ∈ toPieces t v, Val.Avoids U p := by
  intro p hp
  simp only [toPieces, List.mem_map] at hp
  obtain ⟨⟨o, lt⟩, -, rfl⟩ := hp
  exact decode_avoids hU (encode_avoids t h) o lt

theorem outargs_notU (hU : TempU U) (a : Nat) : ¬ U (.outargs a) := by
  intro hu; obtain ⟨n, hn⟩ := hU _ hu; cases hn

/-- `decodeArgs` reads only the outgoing-arguments area. -/
theorem decodeArgs_eqOff (hU : TempU U) (tabs : Tables) (act : Nat) {m m' : Mem}
    (hm : Mem.EqOff U m m') : ∀ (ps : List ABIParam) (pieces : List Val),
      decodeArgs tabs act m' ps pieces = decodeArgs tabs act m ps pieces
  | [], [] => rfl
  | [], _ :: _ => rfl
  | p :: ps, pieces => by
    unfold decodeArgs
    have hr : ∀ o n, m'.read ⟨.outargs act, o⟩ n = m.read ⟨.outargs act, o⟩ n :=
      fun o n => EqOff.read hm ⟨.outargs act, o⟩ n (outargs_notU hU act)
    simp only [hr, decodeArgs_eqOff hU tabs act hm ps]

theorem decodeArgs_avoids (hU : TempU U) (tabs : Tables) (act : Nat) {m : Mem} (hm : m.Avoids U) :
    ∀ (ps : List ABIParam) {pieces args : List Val}, (∀ p ∈ pieces, Val.Avoids U p) →
      decodeArgs tabs act m ps pieces = some args → ∀ a ∈ args, Val.Avoids U a
  | [], [], _, _, hd => by simp only [decodeArgs] at hd; cases hd; simp
  | [], _ :: _, _, _, hd => by simp [decodeArgs] at hd
  | p :: ps, pieces, args, hp, hd => by
    unfold decodeArgs at hd
    dsimp only at hd
    split at hd
    · cases hr : m.read ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (tabs.ty p.type).size with
      | none => rw [hr] at hd; cases hd
      | some bs =>
        rw [hr] at hd
        cases hn : decodeArgs tabs act m ps pieces with
        | none => simp [hn, bind, Option.bind] at hd
        | some r =>
          simp only [hn, bind, Option.bind, pure] at hd
          cases hd
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact decode_avoids hU (read_avoids hm hr (outargs_notU hU act)) 0 _
          · exact decodeArgs_avoids hU tabs act hm ps hp hn a ha
    · split at hd
      · cases hd
      · cases hn : decodeArgs tabs act m ps (pieces.drop p.regs.size) with
        | none => simp [hn, bind, Option.bind] at hd
        | some r =>
          simp only [hn, bind, Option.bind, pure] at hd
          cases hd
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact ofPieces_avoids hU _ fun x hx => hp x (List.mem_of_mem_take hx)
          · exact decodeArgs_avoids hU tabs act hm ps
              (fun x hx => hp x (List.mem_of_mem_drop hx)) hn a ha

/-- `encodeResults` writes the same bytes into the outgoing area on both sides; the source's
memory and pieces avoid `U`. -/
theorem encodeResults_eqOff (hU : TempU U) (tabs : Tables) (act : Nat) :
    ∀ (ps : List ABIParam) (rs : List Val) {m m' : Mem} {r : List Val × Mem},
      Mem.EqOff U m m' → encodeResults tabs act ps rs m = some r →
      ∃ m1', encodeResults tabs act ps rs m' = some (r.1, m1') ∧ Mem.EqOff U r.2 m1' ∧
        ((∀ x ∈ rs, Val.Avoids U x) → m.Avoids U → r.2.Avoids U ∧ ∀ p ∈ r.1, Val.Avoids U p)
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
      rw [if_pos hreg] at he
      cases hw : m.write ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (encode (tabs.ty p.type) x) with
      | none => rw [hw] at he; cases he
      | some m1 =>
        rw [hw] at he
        obtain ⟨m1', hw', hm1⟩ := EqOff.write hm hw
        rw [hw']
        obtain ⟨m2', h1, h2, h3⟩ := encodeResults_eqOff hU tabs act ps xs hm1 he
        refine ⟨m2', h1, h2, fun hx hmA => h3 (fun y hy => hx y (List.mem_cons_of_mem _ hy))
          (memAvoids_write hmA hw fun _ => encode_avoids _ (hx x List.mem_cons_self))⟩
    · next hreg =>
      rw [if_neg hreg] at he
      cases hn : encodeResults tabs act ps xs m with
      | none => simp [hn, bind, Option.bind] at he
      | some q =>
        simp only [hn, bind, Option.bind, pure] at he
        cases he
        obtain ⟨m1', h1, h2, h3⟩ := encodeResults_eqOff hU tabs act ps xs hm hn
        refine ⟨m1', by simp [h1, bind, Option.bind, pure], h2, fun hx hmA => ?_⟩
        obtain ⟨h4, h5⟩ := h3 (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hmA
        refine ⟨h4, fun y hy => ?_⟩
        rcases List.mem_append.1 hy with hy | hy
        · exact toPieces_avoids hU _ (hx x List.mem_cons_self) y hy
        · exact h5 y hy

/-! ## The callee -/

theorem callTarget_snoc (ctx : Ctx) (v : Value) (L : List Val) :
    (∃ c clo R, (∀ y ∈ clo, y ∈ L) ∧ (∀ y ∈ R, y ∈ L) ∧
      ∀ x, callTarget ctx v (L ++ [x]) = (c, clo, R ++ [x])) ∨
    (∀ x, (callTarget ctx v (L ++ [x])).2.2 = []) := by
  by_cases hc : v.op = .ClosureLECall ∨ v.op = .ClosureCall
  · have key : ∀ l, callTarget ctx v l = match l with
        | a :: b :: r => (codeTarget? a, some b, r)
        | l => (v.aux.bind ctx.tabs.callee?, none, l) := by
      intro l; unfold callTarget
      rcases hc with hc | hc <;> rw [hc] <;> rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
    match L with
    | [] => exact .inl ⟨v.aux.bind ctx.tabs.callee?, none, [], by simp, by simp,
        fun x => by rw [key]; rfl⟩
    | [a] => exact .inr fun x => by rw [key]; rfl
    | a :: b :: L' =>
      exact .inl ⟨codeTarget? a, some b, L', by simp, fun y hy => by simp [hy],
        fun x => by rw [key]; rfl⟩
  · by_cases hi : v.op = .InterLECall ∨ v.op = .InterCall
    · have key : ∀ l, callTarget ctx v l = match l with
          | a :: r => (codeTarget? a, none, r)
          | l => (v.aux.bind ctx.tabs.callee?, none, l) := by
        intro l; unfold callTarget
        rcases hi with hi | hi <;> rw [hi] <;> rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
      match L with
      | [] => exact .inr fun x => by rw [key]; rfl
      | a :: L' =>
        exact .inl ⟨codeTarget? a, none, L', by simp, fun y hy => by simp [hy],
          fun x => by rw [key]; rfl⟩
    · have key : ∀ l, callTarget ctx v l = (v.aux.bind ctx.tabs.callee?, none, l) := by
        intro l; unfold callTarget
        split <;> simp_all
      exact .inl ⟨_, none, L, by simp, fun y hy => hy, fun x => by rw [key]⟩

/-- Related call results: a returning source's result avoids `U` and the target returns a
related one; a panicking source's target panics alike with a related memory. -/
def CallRel (U : Blk → Prop) (r r' : Res Val) : Prop :=
  (∀ y, r = .ok y → Val.Avoids U y ∧ ∃ y', r' = .ok y' ∧ VR U y y') ∧
    (∀ e m, r = .panic e m → ∃ m', r' = .panic e m' ∧ Mem.EqOff U m m')

theorem callRel_stuck (msg : String) (r' : Res Val) : CallRel U (.stuck msg) r' :=
  ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem callOp_rest_nil {env : Env} {ctx : Ctx} {v : Value} {argv : List Val}
    (h : (callTarget ctx v argv).2.2 = []) : ∃ msg, callOp env ctx v argv = .stuck msg := by
  unfold callOp
  revert h
  generalize callTarget ctx v argv = T
  rcases T with ⟨c, clo, rest⟩
  intro h
  dsimp only at h ⊢
  subst h
  cases c with
  | none => exact ⟨_, rfl⟩
  | some callee => exact ⟨_, rfl⟩

/-- **A call on related arguments.** -/
theorem callOp_rel {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {v : Value}
    {L : List Val} {w w' : Val} (hw : VR U w w') (hav : ∀ a ∈ L ++ [w], Val.Avoids U a) :
    CallRel U (callOp env ctx v (L ++ [w])) (callOp env ctx v (L ++ [w'])) := by
  rcases callTarget_snoc ctx v L with ⟨c, clo, R, hclo, hR, hT⟩ | hT
  rotate_left
  · obtain ⟨msg, h⟩ := callOp_rest_nil (env := env) (hT w)
    rw [h]; exact callRel_stuck _ _
  unfold callOp
  rw [hT w, hT w']
  dsimp only
  simp only [List.getLast?_concat, List.dropLast_concat]
  cases c with
  | none => exact callRel_stuck _ _
  | some callee =>
  have hwA : Val.Avoids U w := hav w (by simp)
  have hLA : ∀ a ∈ L, Val.Avoids U a := fun a ha => hav a (by simp [ha])
  rcases Classical.em (∃ M, w = .mem M) with ⟨M, rfl⟩ | hwm
  rotate_left
  · have : ∀ M, w ≠ .mem M := fun M h => hwm ⟨M, h⟩
    cases w <;> first | exact absurd rfl (this _) | exact callRel_stuck _ _
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  dsimp only [bind, Res.bind, Res.ofOption]
  have hMA : M.Avoids U := hwA
  have hRA : ∀ a ∈ R, Val.Avoids U a := fun a ha => hLA a (hR a ha)
  have hcloA : ∀ y ∈ clo, Val.Avoids U y := fun y hy => hLA y (hclo y hy)
  have hTemp : ∀ b, U b → ∃ a n, b = .temp a n := fun b hb => by
    obtain ⟨n, hn⟩ := hU b hb; exact ⟨0, n, hn⟩
  rw [decodeArgs_eqOff hU _ _ hm]
  -- the arguments are the same on both sides and avoid `U`
  have core : ∀ (args : List Val), (∀ a ∈ args, Val.Avoids U a) → ∀ (post : Bool),
      CallRel U
        (if (args.any Val.hasPoison || (clo.map Val.hasPoison).getD false) = true then
          Res.stuck (toString "call " ++ toString callee ++ toString ": poison argument")
        else
          Res.bind (Res.ofOption (toString "call " ++ toString callee ++ toString ": no contract")
            (env.extern callee)) fun c =>
          match c args clo M with
          | .returned rs m' =>
            Res.bind (Res.ofOption (toString "call " ++ toString callee ++
                toString ": results do not match the ABI")
              (encodeResults ctx.tabs ctx.act
                (List.filter (fun x => x.out)
                  ((Option.map (fun x => x.params.toList) (callABI? ctx.tabs v.aux)).getD []))
                rs m')) fun x =>
            if post = true then
              .ok (Val.tuple (x.fst ++ [Val.mem x.snd, Val.agg (List.map (fun p =>
                if p.regs.isEmpty = true then Val.ptr ⟨Blk.outargs ctx.act, BitVec.ofInt 64 p.offset⟩
                else Val.poison) (List.filter (fun x => x.out)
                  ((Option.map (fun x => x.params.toList) (callABI? ctx.tabs v.aux)).getD [])))]))
            else
              .ok (Val.tuple (rs ++ [Val.mem x.snd, Val.agg (List.map (fun p =>
                if p.regs.isEmpty = true then Val.ptr ⟨Blk.outargs ctx.act, BitVec.ofInt 64 p.offset⟩
                else Val.poison) (List.filter (fun x => x.out)
                  ((Option.map (fun x => x.params.toList) (callABI? ctx.tabs v.aux)).getD [])))]))
          | .panicked e m' => .panic e m'
          | .stuck msg => .stuck msg)
        (if (args.any Val.hasPoison || (clo.map Val.hasPoison).getD false) = true then
          Res.stuck (toString "call " ++ toString callee ++ toString ": poison argument")
        else
          Res.bind (Res.ofOption (toString "call " ++ toString callee ++ toString ": no contract")
            (env.extern callee)) fun c =>
          match c args clo M' with
          | .returned rs m' =>
            Res.bind (Res.ofOption (toString "call " ++ toString callee ++
                toString ": results do not match the ABI")
              (encodeResults ctx.tabs ctx.act
                (List.filter (fun x => x.out)
                  ((Option.map (fun x => x.params.toList) (callABI? ctx.tabs v.aux)).getD []))
                rs m')) fun x =>
            if post = true then
              .ok (Val.tuple (x.fst ++ [Val.mem x.snd, Val.agg (List.map (fun p =>
                if p.regs.isEmpty = true then Val.ptr ⟨Blk.outargs ctx.act, BitVec.ofInt 64 p.offset⟩
                else Val.poison) (List.filter (fun x => x.out)
                  ((Option.map (fun x => x.params.toList) (callABI? ctx.tabs v.aux)).getD [])))]))
            else
              .ok (Val.tuple (rs ++ [Val.mem x.snd, Val.agg (List.map (fun p =>
                if p.regs.isEmpty = true then Val.ptr ⟨Blk.outargs ctx.act, BitVec.ofInt 64 p.offset⟩
                else Val.poison) (List.filter (fun x => x.out)
                  ((Option.map (fun x => x.params.toList) (callABI? ctx.tabs v.aux)).getD [])))]))
          | .panicked e m' => .panic e m'
          | .stuck msg => .stuck msg) := by
    intro args hargs post
    split
    · exact callRel_stuck _ _
    cases hx : env.extern callee with
    | none => exact callRel_stuck _ _
    | some c =>
    dsimp only [Res.ofOption, Res.bind]
    have hc := hfs callee c hx U hTemp args clo M M' hargs hcloA hMA hm
    revert hc
    generalize c args clo M = o
    generalize c args clo M' = o'
    intro hc
    have haddr : ∀ (ps : List ABIParam), Val.Avoids U (Val.agg (ps.map fun p =>
        if p.regs.isEmpty = true then Val.ptr ⟨Blk.outargs ctx.act, BitVec.ofInt 64 p.offset⟩
        else Val.poison)) := by
      intro ps
      show Val.AvoidsList U _
      rw [avoidsList_iff]
      intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨p, -, rfl⟩ := ha
      split
      · exact outargs_notU hU _
      · trivial
    cases o with
    | stuck msg => exact callRel_stuck _ _
    | panicked e r =>
      cases o' with
      | panicked e' r' =>
        obtain ⟨rfl, -, hrr⟩ := hc
        exact ⟨fun _ h => (nomatch h), fun e1 m1 h => by cases h; exact ⟨r', rfl, hrr⟩⟩
      | returned _ _ => exact hc.elim
      | stuck _ => exact hc.elim
    | returned rs r =>
      cases o' with
      | returned rs' r' =>
        obtain ⟨rfl, hrsA, hrA, hrr⟩ := hc
        dsimp only
        cases he : encodeResults ctx.tabs ctx.act
            (List.filter (fun x => x.out) ((Option.map (fun x => x.params.toList)
              (callABI? ctx.tabs v.aux)).getD [])) rs' r with
        | none => exact callRel_stuck _ _
        | some x =>
          obtain ⟨m1', he', hm1, hA⟩ := encodeResults_eqOff hU ctx.tabs ctx.act _ rs' hrr he
          obtain ⟨hA1, hA2⟩ := hA hrsA hrA
          rw [he']
          dsimp only
          refine ⟨fun y hy => ?_, fun _ _ h => ?_⟩
          · cases post
            · simp only [Bool.false_eq_true, ite_false] at hy ⊢
              cases hy
              refine ⟨?_, _, rfl, .tuple (VRL.append (VRL.refl _)
                (.cons (.mem hm1) (.cons (.refl _) .nil)))⟩
              show Val.AvoidsList U _
              rw [avoidsList_iff]
              intro a ha
              rcases List.mem_append.1 ha with ha | ha
              · exact hrsA a ha
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                rcases ha with rfl | rfl
                · exact hA1
                · exact haddr _
            · simp only [ite_true] at hy ⊢
              cases hy
              refine ⟨?_, _, rfl, .tuple (VRL.append (VRL.refl _)
                (.cons (.mem hm1) (.cons (.refl _) .nil)))⟩
              show Val.AvoidsList U _
              rw [avoidsList_iff]
              intro a ha
              rcases List.mem_append.1 ha with ha | ha
              · exact hA2 a ha
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                rcases ha with rfl | rfl
                · exact hA1
                · exact haddr _
          · cases post <;> simp at h
      | panicked _ _ => exact hc.elim
      | stuck _ => exact hc.elim
  by_cases hp : (v.op == Op.StaticCall || v.op == Op.ClosureCall || v.op == Op.InterCall) = true
  · simp only [hp, ite_true]
    cases hd : decodeArgs ctx.tabs ctx.act M
        (List.filter (fun x => !x.out) ((Option.map (fun x => x.params.toList)
          (callABI? ctx.tabs v.aux)).getD [])) R with
    | none => exact callRel_stuck _ _
    | some args =>
      have := core args (decodeArgs_avoids hU _ _ hMA _ hRA hd) true
      simp only [ite_true] at this
      exact this
  · simp only [hp, Bool.false_eq_true, ite_false]
    have := core R hRA false
    simp only [Bool.false_eq_true, ite_false] at this
    exact this

end GoFV.Proof.DAE
