import GoFV.Proof.Low.SimDen
import GoFV.Proof.CallMono

/-!
# Corresponding atoms evaluate to refinements (issue #385)

The pieces of `GoFV.Proof.Low.atomPair_eval` (`SimMem.lean`): an atom `w` of the lowered function
`g` that corresponds to the atom `u` of `f` (`LowerCheck.atomPair`; `u`'s op is generic) evaluates
(`Sem.evalValueL`, mode of `g`) to a refinement of `u`'s evaluation (mode of `f`) on refined
argument registers:

* the same op: Phase 1's `evalOp_mono`, then the shaping (`rty_le`: Phase 1's `retype` is
  refined by `retypeL`, at the same shape);
* `NilCheck` → `LoweredNilCheck`: `arm64Op` runs `memRoot` of the generic op;
* `GetClosurePtr` → `LoweredGetClosurePtr`: both read the frame's closure;
* the calls `StaticCall`/`ClosureCall`/`InterCall` → `CALLstatic`/`CALLclosure`/`CALLinter`:
  `arm64Op` runs `callOp` of the generic op on the register pieces fitted to their leaves
  (`fitPieces`). A piece `fitPiece` changes is one whose `encode` at its leaf is all `poison`
  (`encode_fitPiece`), so the decoded arguments of the fitted pieces refine those of the pieces
  (`decodeArgs_fit`), and the call on them refines the call (`callOp_fit`).
-/

namespace GoFV.Proof.Low.Sim

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.Low GoFV.Proof.Term GoFV.Proof.AtomSim
  GoFV.Opt.LowerCheck

/-! ## Fitting register pieces -/

/-- A piece `fitPiece` changes encodes as `poison` at its leaf. -/
theorem encode_fitPiece (t : Ty) (x : Val) : BytesRefineA (encode t x) (encode t (fitPiece t x)) := by
  have hp : ∀ y, encode t x = Array.replicate t.size .poison →
      BytesRefineA (encode t x) (encode t y) := fun y h => by
    rw [h]; exact BytesRefineA.replicate_poison _ (encode_size t y)
  unfold fitPiece
  split
  · next w a w' =>
    split
    · exact BytesRefineA.refl _
    · next hne =>
      refine hp _ ?_
      have hne' : (w == w') = false := by simpa using hne
      simp only [encode, hne', Bool.false_eq_true, ite_false, Ty.size]
  · next w a e =>
    split
    · exact BytesRefineA.refl _
    · next hne =>
      refine hp _ ?_
      cases w <;> simp_all [encode, Ty.size]
  · exact hp _ (by simp [encode, Ty.size])
  · exact hp _ (by simp [encode, Ty.size])
  · exact BytesRefineA.refl _

/-- `ofPieces`' fold on pieces changed by `G` at leaves where their encodings refine. -/
theorem fold_fit : ∀ (ls : List (Nat × Ty)) (ps : List Val) (G : Nat → Val → Val),
    (∀ i o t x, ls[i]? = some (o, t) → BytesRefineA (encode t x) (encode t (G i x))) →
    ∀ {buf buf' : Array Byte}, BytesRefineA buf buf' →
      BytesRefineA ((ls.zip ps).foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v)) buf)
        ((ls.zip (ps.mapIdx G)).foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v)) buf')
  | [], _, _, _, _, _, hb => by simpa using hb
  | _ :: _, [], _, _, _, _, hb => by simpa using hb
  | (o, t) :: ls, x :: ps, G, hG, _, _, hb => by
    rw [List.mapIdx_cons, List.zip_cons_cons, List.zip_cons_cons, List.foldl_cons, List.foldl_cons]
    exact fold_fit ls ps (fun i => G (i + 1)) (fun i o' t' x' hi => hG (i + 1) o' t' x' hi)
      (putBytes_mono hb (hG 0 o t x rfl) o)

theorem ofPieces_fit (t : Ty) (ps : List Val) (G : Nat → Val → Val)
    (hG : ∀ i o t' x, (leaves t)[i]? = some (o, t') → BytesRefineA (encode t' x) (encode t' (G i x))) :
    Sem.Refines (ofPieces t ps) (ofPieces t (ps.mapIdx G)) :=
  decode_mono (fold_fit (leaves t) ps G hG (BytesRefineA.refl _)) 0 t

theorem fitPieces_nil (tabs : Tables) : ∀ ps : List ABIParam, fitPieces tabs ps [] = []
  | [] => rfl
  | p :: ps => by
    unfold fitPieces
    split
    · exact fitPieces_nil tabs ps
    · simp [fitPieces_nil tabs ps]

/-- With enough pieces for the parameters, fitting does not touch what follows them. -/
theorem fitPieces_append (tabs : Tables) (act : Nat) (m : Mem) :
    ∀ (ps : List ABIParam) {pieces : List Val} {args : List Val} (l : List Val),
      decodeArgs tabs act m ps pieces = some args →
      fitPieces tabs ps (pieces ++ l) = fitPieces tabs ps pieces ++ l
  | [], pieces, args, l, h => by
    cases pieces with
    | nil => rfl
    | cons => simp [decodeArgs] at h
  | p :: ps, pieces, args, l, h => by
    unfold decodeArgs at h
    dsimp only at h
    unfold fitPieces
    dsimp only
    split
    · next he =>
      rw [if_pos he] at h
      cases hr : m.read ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (tabs.ty p.type).size with
      | none => rw [hr] at h; cases h
      | some bs =>
        rw [hr] at h
        cases hn : decodeArgs tabs act m ps pieces with
        | none => simp [hn, bind, Option.bind] at h
        | some r => exact fitPieces_append tabs act m ps l hn
    · next he =>
      rw [if_neg he] at h
      split at h
      · cases h
      · next hl =>
        cases hn : decodeArgs tabs act m ps (pieces.drop p.regs.size) with
        | none => simp [hn, bind, Option.bind] at h
        | some r =>
          have hle : p.regs.size ≤ pieces.length := by omega
          rw [List.take_append_of_le_length hle, List.drop_append_of_le_length hle,
            fitPieces_append tabs act m ps l hn, List.append_assoc]

/-- `fitPieces` at a register parameter: its leaves' pieces fitted, each one whose encoding at
its leaf is all `poison` or unchanged. -/
theorem fitPieces_cons_reg (tabs : Tables) {p : ABIParam} {ps : List ABIParam} {pieces : List Val}
    (he : ¬ p.regs.isEmpty = true) :
    ∃ G : Nat → Val → Val, fitPieces tabs (p :: ps) pieces =
        (pieces.take p.regs.size).mapIdx G ++ fitPieces tabs ps (pieces.drop p.regs.size) ∧
      ∀ i o t x, (leaves (tabs.ty p.type))[i]? = some (o, t) →
        BytesRefineA (encode t x) (encode t (G i x)) := by
  refine ⟨fun i x => match (leaves (tabs.ty p.type))[i]? with
    | some (_, t) => fitPiece t x
    | none => x, ?_, ?_⟩
  · conv => lhs; unfold fitPieces
    rw [if_neg he]
    rfl
  · intro i o t x hi
    simp only [hi]
    exact encode_fitPiece t x

/-- The decoded arguments of the fitted pieces refine those of the pieces. -/
theorem decodeArgs_fit (tabs : Tables) (act : Nat) (m : Mem) :
    ∀ (ps : List ABIParam) {pieces : List Val} {args : List Val},
      decodeArgs tabs act m ps pieces = some args →
      ∃ args', decodeArgs tabs act m ps (fitPieces tabs ps pieces) = some args' ∧
        RefinesList args args'
  | [], pieces, args, h => by
    cases pieces with
    | nil => simp only [decodeArgs] at h; cases h; exact ⟨[], rfl, .nil⟩
    | cons => simp [decodeArgs] at h
  | p :: ps, pieces, args, h => by
    by_cases he : p.regs.isEmpty = true
    · have hf : fitPieces tabs (p :: ps) pieces = fitPieces tabs ps pieces := by
        simp only [fitPieces, he, ite_true]
      rw [hf]
      unfold decodeArgs at h ⊢
      dsimp only at h ⊢
      rw [if_pos he] at h ⊢
      cases hr : m.read ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (tabs.ty p.type).size with
      | none => rw [hr] at h; cases h
      | some bs =>
        rw [hr] at h
        cases hn : decodeArgs tabs act m ps pieces with
        | none => simp [hn, bind, Option.bind] at h
        | some r =>
          simp only [hn, bind, Option.bind, pure] at h
          cases h
          obtain ⟨r', hn', hrr⟩ := decodeArgs_fit tabs act m ps hn
          exact ⟨_, by simp [hn', bind, Option.bind, pure],
            .cons (Sem.Refines.refl _) hrr⟩
    · obtain ⟨G, hf, hG⟩ := fitPieces_cons_reg tabs (ps := ps) (pieces := pieces) he
      rw [hf]
      unfold decodeArgs at h ⊢
      dsimp only at h ⊢
      rw [if_neg he] at h ⊢
      split at h
      · cases h
      · next hl =>
        cases hn : decodeArgs tabs act m ps (pieces.drop p.regs.size) with
        | none => simp [hn, bind, Option.bind] at h
        | some r =>
          simp only [hn, bind, Option.bind, pure] at h
          cases h
          obtain ⟨r', hn', hrr⟩ := decodeArgs_fit tabs act m ps hn
          have hlen : ((pieces.take p.regs.size).mapIdx G).length = p.regs.size := by
            simp only [List.length_mapIdx, List.length_take]; omega
          have hnl : ¬ (((pieces.take p.regs.size).mapIdx G ++
              fitPieces tabs ps (pieces.drop p.regs.size)).length < p.regs.size) := by
            simp only [List.length_append, hlen]; omega
          rw [if_neg hnl, List.take_left' hlen, List.drop_left' hlen, hn']
          exact ⟨_, rfl, .cons (ofPieces_fit _ _ _ hG) hrr⟩

/-! ## Calls on fitted pieces -/

/-- The input parameters of a call's ABI assignments (as `arm64Op`'s `call` collects them). -/
def insOf (tabs : Tables) (v : Value) : List ABIParam :=
  ((callABI? tabs v.aux).map (·.params.toList.filter (!·.out))).getD []

theorem insOf_eq (tabs : Tables) (v : Value) :
    (((callABI? tabs v.aux).map (·.params.toList)).getD []).filter (!·.out) = insOf tabs v := by
  unfold insOf
  cases callABI? tabs v.aux <;> rfl

/-- The fitted argument list of a post-`expand calls` call with `k` leading non-pieces. -/
def fitArgs (tabs : Tables) (v : Value) (k : Nat) (argv : List Val) : List Val :=
  argv.take k ++ fitPieces tabs (insOf tabs v) (argv.drop k)

/-- The post-`expand calls` generic calls and their leading non-piece arguments. -/
def PostCall (op : Op) (k : Nat) : Prop :=
  (op = .StaticCall ∧ k = 0) ∨ (op = .ClosureCall ∧ k = 2) ∨ (op = .InterCall ∧ k = 1)

theorem callTarget_fit {ctx : Ctx} {v : Value} {k : Nat} (hc : PostCall v.op k) (argv : List Val) :
    ∃ R, callTarget ctx v (fitArgs ctx.tabs v k argv) =
      ((callTarget ctx v argv).1, (callTarget ctx v argv).2.1, R) ∧
      (R = fitPieces ctx.tabs (insOf ctx.tabs v) (callTarget ctx v argv).2.2 ∨
        R = (callTarget ctx v argv).2.2) := by
  unfold fitArgs
  rcases hc with ⟨hop, rfl⟩ | ⟨hop, rfl⟩ | ⟨hop, rfl⟩
  · refine ⟨_, ?_, .inl rfl⟩
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    unfold callTarget; rw [hop]
  · rcases argv with _ | ⟨a, _ | ⟨b, r⟩⟩
    · refine ⟨_, ?_, .inr rfl⟩
      (simp only [List.take_nil, List.drop_nil, fitPieces_nil, List.append_nil]) <;> rfl
    · refine ⟨_, ?_, .inr rfl⟩
      (simp only [List.take, List.drop, fitPieces_nil, List.append_nil]) <;> rfl
    · refine ⟨_, ?_, .inl rfl⟩
      simp only [List.take, List.drop, List.cons_append, List.nil_append]
      unfold callTarget; rw [hop]
  · rcases argv with _ | ⟨a, r⟩
    · refine ⟨_, ?_, .inr rfl⟩
      (simp only [List.take_nil, List.drop_nil, fitPieces_nil, List.append_nil]) <;> rfl
    · refine ⟨_, ?_, .inl rfl⟩
      simp only [List.take, List.drop, List.cons_append, List.nil_append]
      unfold callTarget; rw [hop]

private theorem eq_dropLast_of_getLast? {l : List Val} {x : Val} (h : l.getLast? = some x) :
    l = l.dropLast ++ [x] := by
  have hne : l ≠ [] := by rintro rfl; cases h
  rw [List.getLast?_eq_getLast hne] at h
  obtain rfl := Option.some.inj h
  exact (List.dropLast_concat_getLast hne).symm

private theorem resRefines_trans {a b c : Res Val} (h1 : Res.Refines a b) (h2 : Res.Refines b c) :
    Res.Refines a c := by
  cases h1 with
  | ok h => cases h2 with | ok h' => exact .ok (h.trans h')
  | panic e hm => cases h2 with | panic e hm' => exact .panic e (hm.trans hm')
  | stuck msg => exact .stuck msg _

/-- **A call on its fitted pieces refines the call.** -/
theorem callOp_fit {env : Env} (hE : env.Mono) (ctx : Ctx) (v : Value) {k : Nat}
    (hc : PostCall v.op k) (argv : List Val) :
    Res.Refines (callOp env ctx v argv) (callOp env ctx v (fitArgs ctx.tabs v k argv)) := by
  have hpost : (v.op == Op.StaticCall || v.op == Op.ClosureCall || v.op == Op.InterCall) = true := by
    rcases hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
  obtain ⟨R, hR, hRr⟩ := callTarget_fit (ctx := ctx) hc argv
  rcases hRr with hRr | hRr
  case inr =>
    have heq : callTarget ctx v (fitArgs ctx.tabs v k argv) = callTarget ctx v argv := by
      rw [hR, hRr]
    unfold callOp; rw [heq]; exact Res.Refines.refl _
  unfold callOp
  rw [hR, hRr]
  generalize callTarget ctx v argv = T
  rcases T with ⟨callee?, clo, rest⟩
  dsimp only
  dsimp only [bind, Res.bind, Res.ofOption]
  cases hl : rest.getLast? with
  | none => exact .stuck _ _
  | some last =>
    cases last with
    | mem m =>
      dsimp only
      simp only [hpost, ↓reduceIte, insOf_eq]
      cases hd : decodeArgs ctx.tabs ctx.act m (insOf ctx.tabs v) rest.dropLast with
      | none => exact .stuck _ _
      | some args =>
        have hrest : rest = rest.dropLast ++ [.mem m] := eq_dropLast_of_getLast? hl
        have hfit : fitPieces ctx.tabs (insOf ctx.tabs v) rest =
            fitPieces ctx.tabs (insOf ctx.tabs v) rest.dropLast ++ [.mem m] := by
          conv => lhs; rw [hrest]
          exact fitPieces_append ctx.tabs ctx.act m _ _ hd
        rw [hfit, List.getLast?_concat, List.dropLast_concat]
        dsimp only
        obtain ⟨args', hd', ha⟩ := decodeArgs_fit ctx.tabs ctx.act m _ hd
        rw [hd']
        dsimp only
        revert ha
        generalize args = A
        generalize args' = A'
        intro ha
        split
        · exact .stuck _ _
        · next hp =>
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
          have hp1 := ha.any_hasPoison hp.1
          simp only [hp1, hp.2, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
          split
          · exact .stuck _ _
          split
          · exact .panic _ (Mem.Refines.refl _)
          cases callee? with
          | none => exact .stuck _ _
          | some callee =>
            dsimp only
            cases hx : (env.atAct ctx.act).extern callee with
            | none => exact .stuck _ _
            | some c =>
              dsimp only
              generalize callFrame ctx.tabs v.aux _ _ = F
              have hclo : OptRefines clo clo := by
                cases clo with
                | none => exact .none
                | some c => exact .some (Sem.Refines.refl _)
              have := hE.atAct ctx.act _ _ hx hp.1 hp.2 ha hclo
                ((Mem.Refines.refl m).poisonBelow (.outargs ctx.act) F)
              revert this
              generalize c A clo (m.poisonBelow (.outargs ctx.act) F) = o
              generalize c A' clo (m.poisonBelow (.outargs ctx.act) F) = o'
              intro ho
              cases ho with
              | returned hr0 hm' =>
                dsimp only
                cases he : encodeResults ctx.tabs ctx.act _ _ _ with
                | none => exact .stuck _ _
                | some r =>
                  obtain ⟨r', he', hr1, hr2⟩ := encodeResults_mono ctx.tabs ctx.act _
                    (retypeResults_mono ctx.tabs _ hr0) hm' he
                  rw [he']
                  dsimp only
                  exact .ok (.tuple (hr1.append (.cons (.mem hr2) (.cons (Sem.Refines.refl _) .nil))))
              | panicked e hm' => exact .panic e hm'
              | stuck msg o => exact .stuck _ _
    | _ => exact .stuck _ _

/-! ## Renamed atoms -/

theorem renameOp_cases {a b : Op} (h : renameOp a b = true) :
    (a = .NilCheck ∧ b = .ARM64LoweredNilCheck) ∨ (a = .StaticCall ∧ b = .ARM64CALLstatic) ∨
      (a = .ClosureCall ∧ b = .ARM64CALLclosure) ∨ (a = .InterCall ∧ b = .ARM64CALLinter) ∨
      (a = .GetClosurePtr ∧ b = .ARM64LoweredGetClosurePtr) := by
  unfold renameOp at h
  split at h <;> simp_all

/-- A renamed atom evaluates as the generic op it renames (`arm64Op`), on fitted pieces for a
call. -/
theorem evalOpL_rename {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {argv : List Val} {ty : Ty}
    {o : Op} (h : renameOp o w.op = true) :
    (∃ k, PostCall o k ∧ evalOpL false env ctx fr w argv ty =
        callOp env ctx { w with op := o } (fitArgs ctx.tabs { w with op := o } k argv)) ∨
      ((o = .NilCheck ∨ o = .GetClosurePtr) ∧
        evalOpL false env ctx fr w argv ty = evalOp env ctx fr { w with op := o } argv ty) := by
  have h0 : nilFaults false ctx w argv = none := rfl
  rcases renameOp_cases h with ⟨rfl, hw⟩ | ⟨rfl, hw⟩ | ⟨rfl, hw⟩ | ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · refine .inr ⟨.inl rfl, ?_⟩
    have hg : Op.ARM64LoweredNilCheck.generic = false := by decide
    unfold evalOpL
    rw [hw]
    simp only [hg, Bool.false_eq_true, ite_false]
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw]
    unfold evalOp
    rfl
  · refine .inl ⟨0, .inl ⟨rfl, rfl⟩, ?_⟩
    have hg : Op.ARM64CALLstatic.generic = false := by decide
    unfold evalOpL
    rw [hw]
    simp only [hg, Bool.false_eq_true, ite_false]
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw]
    rfl
  · refine .inl ⟨2, .inr (.inl ⟨rfl, rfl⟩), ?_⟩
    have hg : Op.ARM64CALLclosure.generic = false := by decide
    unfold evalOpL
    rw [hw]
    simp only [hg, Bool.false_eq_true, ite_false]
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw]
    rfl
  · refine .inl ⟨1, .inr (.inr ⟨rfl, rfl⟩), ?_⟩
    have hg : Op.ARM64CALLinter.generic = false := by decide
    unfold evalOpL
    rw [hw]
    simp only [hg, Bool.false_eq_true, ite_false]
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw]
    rfl
  · refine .inr ⟨.inr rfl, ?_⟩
    have hg : Op.ARM64LoweredGetClosurePtr.generic = false := by decide
    unfold evalOpL
    rw [hw]
    simp only [hg, Bool.false_eq_true, ite_false]
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw]
    unfold evalOp
    rfl

/-- A call of a post-`expand calls` generic op evaluates by `callOp`. -/
theorem evalOp_postCall {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {k : Nat} (hc : PostCall v.op k) : evalOp env ctx fr v argv ty = callOp env ctx v argv := by
  rcases hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> (unfold evalOp; rw [h])

end GoFV.Proof.Low.Sim
