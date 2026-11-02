import GoFV.Proof.Pass.WBLocal
import GoFV.Proof.Pass.SegCall
import GoFV.Proof.Pass.ECCall

/-!
# writebarrier: the write-barrier helper calls (issue #36)

`runtime.wbZero(typ, dst)`/`runtime.wbMove(typ, dst, src)` in a run's buffer block: on an
environment whose helpers are the runtime's and do not spill (`WbHelpers`), a call with words in
its `uintptr` registers (a pointer or a 64-bit integer, `WordV`: `decodeArgs` gives no `poison`)
returns the memory it is given (`callOp_wb`: `Runtime.wbHelper`, and a no-spill callee with
register arguments only owns no part of the caller's outgoing-arguments area, `callFrame … false
= 0`). The local steps: the type address `Addr {type:T} SB` (`local_taddr`), the call
(`local_call`) and its memory `SelectN [0]` (`local_seln`).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

/-- A value a helper takes in a `uintptr` register: a pointer or a 64-bit integer. -/
def WordV : Val → Prop
  | .ptr _ => True
  | .int .w64 _ => True
  | _ => False

theorem wordV_of_asPtrWord {a : Val} {p : Ptr} (h : a.asPtrWord = some p) : WordV a := by
  cases a with
  | ptr q => trivial
  | int w x => cases w <;> simp_all [Val.asPtrWord, WordV]
  | _ => simp [Val.asPtrWord] at h

theorem ofPieces_word {z : Val} (h : WordV z) : (ofPieces (.int .w64) [z]).hasPoison = false := by
  cases z with
  | ptr q =>
    rw [EC.ecc_ofPieces_ptr]
    show q.word.hasPoison = false
    rcases Ptr.word_cases q with ⟨-, hw⟩ | ⟨-, a, -, hw⟩ <;> rw [hw] <;> rfl
  | int w x =>
    cases w <;> simp only [WordV] at h
    rw [Seg.ofPieces_int]; rfl
  | _ => cases h

/-- A parameter of a helper, as `wbParam` checks it. -/
theorem wbParam_spec {tabs : Tables} {p : ABIParam} (h : wbParam tabs p = true) :
    p.out = false ∧ p.regs.size = 1 ∧ tabs.ty p.type = .int .w64 := by
  unfold wbParam at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · assumption
  · cases h3

theorem decodeArgs_words {tabs : Tables} {act : Nat} {m : Mem} :
    ∀ (ps : List ABIParam) (zs : List Val), ps.length = zs.length →
      (∀ p ∈ ps, wbParam tabs p = true) → (∀ z ∈ zs, WordV z) →
      ∃ as, decodeArgs tabs act m ps zs = some as ∧ as.any Val.hasPoison = false
  | [], [], _, _, _ => ⟨[], rfl, rfl⟩
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | p :: ps, z :: zs, h, hp, hz => by
    obtain ⟨-, hr, ht⟩ := wbParam_spec (hp p List.mem_cons_self)
    obtain ⟨as, has, hnp⟩ := decodeArgs_words ps zs (by simpa using h)
      (fun q hq => hp q (List.mem_cons_of_mem _ hq)) (fun y hy => hz y (List.mem_cons_of_mem _ hy))
    refine ⟨ofPieces (tabs.ty p.type) [z] :: as, ?_, ?_⟩
    · rw [Seg.decodeArgs_reg hr, has]; rfl
    · rw [List.any_cons, ht, ofPieces_word (hz z List.mem_cons_self), hnp]; rfl

theorem poisonBelow_zero (m : Mem) (b : Blk) : m.poisonBelow b 0 = m := by
  unfold Mem.poisonBelow
  split
  · rename_i a ha
    have hd : a.data.mapIdx (fun i x => if i < 0 then Byte.poison else x) = a.data := by
      apply Array.ext
      · simp
      · intro i h1 h2; simp
    rw [hd]
    exact DSE.set_self ha
  · rfl

/-- The frame of a call whose parameters are all in registers ends at 0 when its callee does not
spill. -/
theorem callFrame_regs {tabs : Tables} {aux : Option AuxRef} {ps : List ABIParam}
    (h : ∀ p ∈ ps, p.regs.isEmpty = false) : callFrame tabs aux ps false = 0 := by
  unfold callFrame
  simp only [Bool.false_eq_true, ite_false]
  generalize 0 = n
  induction ps generalizing n with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons, if_neg (by simp [h p List.mem_cons_self])]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) n

private theorem res_ok_bind {α β : Type} (a : α) (k : α → Res β) : (Res.ok a >>= k) = k a := rfl

/-- **A helper call returns its memory.** -/
theorem callOp_wb {env : Env} {ctx : Sem.Ctx} {w : Value} {L : List Val} {m : Mem}
    {name : String} {abi : CallABI} (hW : WbHelpers env) (hop : w.op = .StaticCall)
    (hname : w.aux.bind ctx.tabs.callee? = some name)
    (hn : name = "runtime.wbZero" ∨ name = "runtime.wbMove")
    (habi : callABI? ctx.tabs w.aux = some abi)
    (hps : ∀ p ∈ abi.params.toList, wbParam ctx.tabs p = true)
    (hlen : abi.params.size = L.length) (hL : ∀ z ∈ L, WordV z) :
    callOp env ctx w (L ++ [.mem m]) = .ok (.tuple [.mem m, .agg []]) := by
  have hins : abi.params.toList.filter (!·.out) = abi.params.toList :=
    List.filter_eq_self.2 fun p hp => by simp [(wbParam_spec (hps p hp)).1]
  have houts : abi.params.toList.filter (·.out) = [] :=
    List.filter_eq_nil_iff.2 fun p hp => by simp [(wbParam_spec (hps p hp)).1]
  obtain ⟨as, hdec, hnp⟩ := decodeArgs_words (tabs := ctx.tabs) (act := ctx.act) (m := m)
    abi.params.toList L (by simpa using hlen) hps hL
  have hreg : ∀ p ∈ abi.params.toList, p.regs.isEmpty = false := fun p hp => by
    simp [Array.isEmpty, (wbParam_spec (hps p hp)).2.1]
  have hoa : outargsOK ctx.tabs ctx.act m abi.params.toList = true := by
    unfold outargsOK
    rw [List.all_eq_true]
    intro p hp
    simp [hreg p hp]
  have hext : (env.atAct ctx.act).extern name = some Runtime.wbHelper := by
    have hd : isDeferName name = false := by
      rcases hn with rfl | rfl <;> decide
    rw [Env.atAct_extern_of hd]
    rcases hn with rfl | rfl
    · exact hW.1
    · exact hW.2.1
  have hsp : env.noSpill name = true := by
    rcases hn with rfl | rfl
    · exact hW.2.2.1
    · exact hW.2.2.2
  have hfr : callFrame ctx.tabs w.aux abi.params.toList (!env.noSpill name) = 0 := by
    rw [hsp]; exact callFrame_regs hreg
  unfold callOp
  simp only [callTarget, hop, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    List.dropLast_concat, habi, Option.map_some, Option.getD_some, hins, houts, res_ok_bind]
  simp only [beq_self_eq_true, Bool.true_or, ite_true, Res.ofOption, hdec, res_ok_bind, hnp,
    Option.map_none, Option.getD_none, Bool.or_false, Bool.false_eq_true, ite_false, hoa,
    Bool.not_true, nilClosure_none, hname, hext, hfr, poisonBelow_zero]
  rfl

/-- `Addr {sym} …` points to the start of the global `sym`. -/
theorem frameVal_sym {tabs : Tables} {g : Func} {w : Value} {s : String} (hop : w.op = .Addr)
    (h : symName? tabs w.aux = some s) :
    frameVal (Ctx.make tabs g) w = some (.ptr ⟨.global s, 0⟩) := by
  unfold symName? at h
  unfold frameVal
  rw [hop]
  dsimp only
  split at h
  · rename_i name _ _ _ he
    simp only [Ctx.make]
    rw [he]
    simp only [Option.some.injEq] at h
    simp [h]
  · cases h

/-- **The type address** of a helper call: a pointer to the start of a global. -/
theorem local_taddr {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} {j : Nat} (hw : g.value? x = some w) (hid : w.id = x)
    (hrole : c.roleOf rs x = .taddr j) (hop : w.op = .Addr)
    (hsym : (symName? tabs w.aux).isSome = true) (hty : tabs.ty w.type = .int .w64) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨L, hL⟩ := regsAre_of (g := g') (l := w.args.toList)
    fun a ha => (argQ hw hA (Array.mem_toList_iff.1 ha)).imp fun _ h => h.1
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hsym
  refine ⟨.ptr ⟨.global s, 0⟩, ?_, by simp only [QR, hrole]; exact ⟨_, rfl⟩⟩
  rw [stepV_eq hw, evalValue_of hL, tys_get hw hid, hty]
  have hev : evalOp env (Ctx.make tabs g) g' w L (.int .w64) = .ok (.ptr ⟨.global s, 0⟩) := by
    unfold evalOp
    rw [hop]
    dsimp only
    rw [frameVal_sym hop hs]
    rfl
  rw [hev]
  rfl

theorem regsAre_snoc {g : Frame} : ∀ {l : List ID} {L : List Val} {a : ID} {z : Val},
    RegsAre g l L → g.regs[a]? = some (some z) → RegsAre g (l ++ [a]) (L ++ [z])
  | [], [], _, _, _, h => ⟨h, trivial⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim
  | _ :: _, _ :: _, _, _, ⟨h1, h2⟩, h => ⟨h1, regsAre_snoc h2 h⟩

/-- **A helper call**: the run's memory (with or without a buffer) is returned unchanged. -/
theorem local_call {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} (hW : WbHelpers env) {x : ID} {w : Value} {j : Nat} {name : String}
    {abi : CallABI} (hw : g.value? x = some w) (hid : w.id = x) (hrole : c.roleOf rs x = .call j)
    (hop : w.op = .StaticCall) (hty : tabs.ty w.type = .tuple [.mem])
    (hname : w.aux.bind tabs.callee? = some name)
    (hn : name = "runtime.wbZero" ∨ name = "runtime.wbMove")
    (habi : callABI? tabs w.aux = some abi) (hps : ∀ p ∈ abi.params.toList, wbParam tabs p = true)
    {as : List ID} {mm : ID} (hargs : w.args.toList = as ++ [mm]) (hlen : abi.params.size = as.length)
    (hword : ∀ a ∈ as, ∀ z, QR c rs Gr a z → WordV z)
    (hmem : ∀ z, QR c rs Gr mm z →
      ∃ r M m, rs[j]? = some r ∧ MemAt Gr r.sp.mem M ∧ z = .mem m ∧ BufW M m) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  have hA' : ∀ a ∈ w.args.toList, ∃ z, g'.regs[a]? = some (some z) ∧ QR c rs Gr a z :=
    fun a ha => argQ hw hA (Array.mem_toList_iff.1 ha)
  rw [hargs] at hA'
  obtain ⟨L, hL⟩ := regsAre_of (g := g') (l := as)
    fun a ha => (hA' a (List.mem_append_left _ ha)).imp fun _ h => h.1
  obtain ⟨zm, hzm, hqm⟩ := hA' mm (by simp)
  obtain ⟨r, M, m, hr, hM, rfl, hB⟩ := hmem zm hqm
  have hLw : ∀ z ∈ L, WordV z := by
    intro z hz
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hz
    have hkl : k < as.length := by
      have := (List.getElem?_eq_some_iff.1 hk).1; rw [regsAre_length hL] at this; exact this
    obtain ⟨a, ha⟩ : ∃ a, as[k]? = some a := ⟨_, List.getElem?_eq_getElem hkl⟩
    obtain ⟨z', hz', hr'⟩ := regsAre_get hL ha
    rw [hk] at hz'; cases hz'
    obtain ⟨z'', hz'', hq⟩ := hA' a (List.mem_append_left _ (List.mem_of_getElem? ha))
    rw [hr'] at hz''; cases hz''
    exact hword a (List.mem_of_getElem? ha) _ hq
  have hLm : RegsAre g' w.args.toList (L ++ [.mem m]) := by
    rw [hargs]; exact regsAre_snoc hL hzm
  refine ⟨.tuple [.mem m, .agg []], ?_, ?_⟩
  · rw [stepV_eq hw, evalValue_of hLm, tys_get hw hid, hty]
    have hev : evalOp env (Ctx.make tabs g) g' w (L ++ [.mem m]) (.tuple [.mem]) =
        callOp env (Ctx.make tabs g) w (L ++ [.mem m]) := by
      simp only [evalOp, hop]
    rw [hev, callOp_wb hW hop hname hn habi hps (by rw [hlen, regsAre_length hL]) hLw]
    rfl
  · simp only [QR, hrole]
    exact ⟨r, M, m, hr, hM, rfl, hB⟩

/-- **The call's memory** `SelectN [0]`. -/
theorem local_seln {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} {j : Nat} {a : ID} (hw : g.value? x = some w)
    (hid : w.id = x) (hrole : c.roleOf rs x = .seln j) (hop : w.op = .SelectN)
    (hargs : w.args = #[a]) (hai : w.auxInt = 0) (hty : tabs.ty w.type = .mem)
    (ha : c.roleOf rs a = .call j) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨z, hz, hq⟩ := argQ hw hA (a := a) (by rw [hargs]; simp)
  simp only [QR, ha] at hq
  obtain ⟨r, M, m, hr, hM, rfl, hB⟩ := hq
  refine ⟨.mem m, ?_, by simp only [QR, hrole]; exact ⟨r, M, m, hr, hM, rfl, hB⟩⟩
  rw [stepV_eq hw, evalValue_of (L := [_]) (by rw [hargs]; exact ⟨hz, trivial⟩),
    tys_get hw hid, hty, DAE.evalOp_pureOp (.inr (.inr (.inr (.inl hop)))), hop, hai]
  rfl

end GoFV.Proof.WB
