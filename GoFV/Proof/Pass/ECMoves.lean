import GoFV.Proof.Pass.ECStack

/-!
# `expand calls`: chains of `Move`s of wide stack arguments (issue #28)

A call with several wide stack arguments copies each of the leading ones with its own new `Move`
into its slot of the outgoing-arguments area, chained bottom first on the source call's memory
(`ECCheck.callMoves`, `moveChain`). A `Move` above another reads a frame variable
(`ECCheck.localSrcOK`: a `LocalAddr`, whose pointer is outside the area), so it reads the bytes of
the source call's memory (`ecm_moves`):

* the chain's moves keep every allocation's writability and size (`ecm_attr`), so each move's
  read and write succeed once the source has reached the call (`ECCall.ecc_moveObl`);
* the moves write their slots in order and the slots read back the copied bytes, unchanged by
  the later moves and stores of higher slots (`ecm_moves`, `ecm_read_writeAll`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.AtomSim GoFV.Proof.CSE.Mem

/-! ## The chain -/

/-- One step of a chain of `Move`s. -/
theorem ecm_step {g : Func} {nw : ID → Bool} {n : Nat} {z b : ID} {ms : List ID}
    (h : moveChain g nw (n + 1) z b = some ms) :
    (z = b ∧ ms = []) ∨ ∃ w ms', z ≠ b ∧ g.value? z = some w ∧ nw z = true ∧ w.op = .Move ∧
      w.args.size = 3 ∧ moveChain g nw n w.args[2]! b = some ms' ∧ ms = ms' ++ [z] := by
  unfold moveChain at h
  split at h
  · next hzb => cases h; exact .inl ⟨beq_iff_eq.1 hzb, rfl⟩
  · next hzb =>
    split at h
    · next w hw =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        cases hs : moveChain g nw n w.args[2]! b with
        | none => rw [hs] at h; cases h
        | some ms' =>
          rw [hs] at h
          cases h
          exact .inr ⟨w, ms', fun he => hzb (beq_iff_eq.2 he), hw, hc.1.1, hc.1.2, hc.2, hs, rfl⟩
      · cases h
    · cases h

theorem ecm_nil {g : Func} {nw : ID → Bool} :
    ∀ {n : Nat} {z b : ID}, moveChain g nw n z b = some [] → z = b
  | 0, _, _, h => by simp [moveChain] at h
  | n + 1, z, b, h => by
    rcases ecm_step h with ⟨h1, -⟩ | ⟨w, ms', -, -, -, -, -, -, h2⟩
    · exact h1
    · simp at h2

theorem ecm_new {g : Func} {nw : ID → Bool} {n : Nat} {z b : ID} {ms : List ID}
    (h : moveChain g nw n z b = some ms) (hne : ms ≠ []) : nw z = true := by
  match n, h with
  | 0, h => simp [moveChain] at h
  | n + 1, h =>
    rcases ecm_step h with ⟨-, rfl⟩ | ⟨w, ms', -, -, hnw, -⟩
    · exact absurd rfl hne
    · exact hnw

/-- The top of a non-empty chain is its last `Move`. -/
theorem ecm_last {g : Func} {nw : ID → Bool} {n : Nat} {z b : ID} {ms : List ID}
    (h : moveChain g nw n z b = some ms) (hne : ms ≠ []) : ms.getLast? = some z := by
  match n, h with
  | 0, h => simp [moveChain] at h
  | n + 1, h =>
    rcases ecm_step h with ⟨-, rfl⟩ | ⟨w, ms', -, -, -, -, -, -, rfl⟩
    · exact absurd rfl hne
    · simp

theorem ecm_top {g : Func} {nw : ID → Bool} {n : Nat} {top b : ID} {ms : List ID}
    (h : moveChain g nw n top b = some ms) (hne : ms ≠ []) :
    top ∈ ms ∧ ∃ w, g.value? top = some w ∧ w.op = .Move := by
  match n, h with
  | 0, h => simp [moveChain] at h
  | n + 1, h =>
    rcases ecm_step h with ⟨-, rfl⟩ | ⟨w, ms', -, hw, -, hop, -, -, rfl⟩
    · exact absurd rfl hne
    · exact ⟨by simp, w, hw, hop⟩

/-- A `Move` of a chain heads the chain below it, a prefix of the chain. -/
theorem ecm_mem {g : Func} {nw : ID → Bool} :
    ∀ {n : Nat} {top b : ID} {ms : List ID}, moveChain g nw n top b = some ms → ∀ {z : ID}, z ∈ ms →
      ∃ wz n' ms', g.value? z = some wz ∧ nw z = true ∧ wz.op = .Move ∧ wz.args.size = 3 ∧
        moveChain g nw n' wz.args[2]! b = some ms' ∧ ∃ rest, ms = ms' ++ [z] ++ rest
  | 0, _, _, _, h, _, _ => by simp [moveChain] at h
  | n + 1, top, b, ms, h, z, hz => by
    rcases ecm_step h with ⟨-, rfl⟩ | ⟨w, ms', -, hw, hnw, hop, hsz, hc, rfl⟩
    · exact absurd hz List.not_mem_nil
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨wz, n', ms'', h1, h2, h3, h4, h5, rest, hr⟩ := ecm_mem hc hz
      exact ⟨wz, n', ms'', h1, h2, h3, h4, h5, rest ++ [top], by rw [hr]; simp⟩
    · rw [List.mem_singleton.1 hz]
      exact ⟨w, n, ms', hw, hnw, hop, hsz, hc, [], by simp⟩

/-- The `Move`s of a chain whose top is a new value of `E` are new values of `E`. -/
theorem ecm_E {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    ∀ (n : Nat) {z b : ID} {ms : List ID}, moveChain g (isNewB f) n z b = some ms →
      (ms ≠ [] → E z ∧ L z) → ∀ z' ∈ ms, E z' ∧ L z'
  | 0, _, _, _, h, _, _, _ => by simp [moveChain] at h
  | n + 1, z, b, ms, h, hEL, z', hz' => by
    rcases ecm_step h with ⟨-, rfl⟩ | ⟨w, ms', -, hw, -, -, hsz, hc, rfl⟩
    · exact absurd hz' List.not_mem_nil
    have hz := hEL (by simp)
    rcases List.mem_append.1 hz' with hz' | hz'
    · refine ecm_E hNC hL n hc (fun hne => ?_) z' hz'
      obtain ⟨-, w', -, hw', hcl, -⟩ := hNC z hz.1
      change g.value? z = some w' at hw'
      rw [hw] at hw'; cases hw'
      have hm2 : w.args[2]! ∈ w.args := by rw [← Array.mem_toList_iff, ecs_args_three hsz]; simp
      have hn := ecm_new hc hne
      exact ⟨hcl _ hm2 hn, (hL z hz.2 w hw).2 _ hm2 hn⟩
    · rw [List.mem_singleton.1 hz']; exact hz

/-- The top of a chain of `Move`s is a memory with the bottom's writable ranges and sizes. -/
theorem ecm_attr {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    ∀ (n : Nat) {z b : ID} {ms : List ID}, moveChain g (isNewB f) n z b = some ms →
      (ms ≠ [] → E z ∧ L z) → (∀ z' ∈ ms, shapeOf (typeShapes tabs) g z' = .mem) →
      ∀ M, rv T b = .mem M → ∃ M', rv T z = .mem M' ∧
        ∀ blk, (M'.find? blk).map ecsAttr = (M.find? blk).map ecsAttr
  | 0, _, _, _, h, _, _, _, _ => by simp [moveChain] at h
  | n + 1, z, b, ms, h, hEL, hsh, M, hM => by
    rcases ecm_step h with ⟨rfl, rfl⟩ | ⟨w, ms', -, hw, -, hop, hsz, hc, rfl⟩
    · exact ⟨M, hM, fun _ => rfl⟩
    obtain ⟨hEz, hLz⟩ := hEL (by simp)
    obtain ⟨-, w', y, hw', hcl, hy, hev⟩ := hNC z hEz
    change g.value? z = some w' at hw'
    rw [hw] at hw'; cases hw'
    obtain ⟨hwid, hLcl⟩ := hL z hLz w hw
    have hargs := ecs_args_three hsz
    have hm2 : w.args[2]! ∈ w.args := by rw [← Array.mem_toList_iff, hargs]; simp
    have hty : (Ctx.make tabs g).tys[w.id]?.getD .other = .mem := by
      rw [hwid, ← shapeOf_eq]; exact hsh z (by simp)
    obtain ⟨d, s, M0, bs, M1, hd, hs, hM0, hrd, hW, rfl⟩ := ecs_move_val hop hargs hty hev
    have hEL' : ms' ≠ [] → E w.args[2]! ∧ L w.args[2]! := fun hne => by
      have hn := ecm_new hc hne
      exact ⟨hcl _ hm2 hn, hLcl _ hm2 hn⟩
    obtain ⟨M0', hM0', hA⟩ := ecm_attr hNC hL n hc hEL'
      (fun z' hz' => hsh z' (List.mem_append_left _ hz')) M hM
    rw [hM0] at hM0'; cases hM0'
    exact ⟨M1, rv_of hy, fun blk => (ecs_find_write hW blk).trans (hA blk)⟩

/-! ## Memories -/

/-- A read that succeeds succeeds in a memory with the same allocation sizes. -/
theorem ecm_read_congr {m m' : Mem} (h : ∀ b, (m'.find? b).map ecsAttr = (m.find? b).map ecsAttr)
    {p : Ptr} {n : Nat} {bs : Array Byte} (hr : m.read p n = some bs) :
    ∃ bs', m'.read p n = some bs' := by
  unfold Mem.read at hr ⊢
  by_cases hn : n = 0
  · simp [hn]
  simp only [beq_iff_eq, hn, ite_false, Option.bind_eq_bind] at hr ⊢
  have hb := h p.blk
  cases h1 : m.find? p.blk with
  | none => rw [h1] at hr; cases hr
  | some a =>
    rw [h1] at hr hb
    cases h2 : m'.find? p.blk with
    | none => rw [h2] at hb; cases hb
    | some a' =>
      rw [h2] at hb
      simp only [Option.map_some, Option.some.injEq, ecsAttr, Prod.mk.injEq] at hb
      simp only [Option.bind_some] at hr ⊢
      split at hr
      · next hc => rw [ite_eq_left (by rw [hb.2]; exact hc)]; exact ⟨_, rfl⟩
      · cases hr

/-- **A slot read back survives the writes of later slots** (the stores above the `Move`s). -/
theorem ecm_read_writeAll {o0 n : Nat} {bs : Array Byte} (ho : o0 < 2 ^ 24) :
    ∀ {ss : List (Int × Ty)} {ys : List Val} {M Mt : Mem}, M.read (ecsSlot o0) n = some bs →
      writeAll M (List.zipWith ecsW ss ys) = some Mt →
      (∀ s ∈ ss, ((o0 + n : Nat) : Int) ≤ s.1 ∧ s.1 < 2 ^ 24) →
      Mt.read (ecsSlot o0) n = some bs
  | [], _, M, Mt, hr, hw, _ => by
    simp only [List.zipWith_nil_left, writeAll] at hw; cases hw; exact hr
  | _ :: _, [], M, Mt, hr, hw, _ => by
    simp only [List.zipWith_nil_right, writeAll] at hw; cases hw; exact hr
  | s :: ss, y :: ys, M, Mt, hr, hw, hle => by
    rw [List.zipWith_cons_cons] at hw
    simp only [writeAll] at hw
    cases hw1 : M.write (ecsW s y).1 (ecsW s y).2 with
    | none => rw [hw1] at hw; cases hw
    | some M1 =>
      rw [hw1] at hw
      refine ecm_read_writeAll ho ?_ hw fun s' hs' => hle s' (List.mem_cons_of_mem _ hs')
      rw [read_write_sep hw1]
      · exact hr
      have h := hle s List.mem_cons_self
      refine .inr (.inr (.inr (.inl ?_)))
      simp only [ecsW, ecsSlot, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-- **The chain of `Move`s writes its slots in order** (`sp`: the parameters they copy, bottom
first, of sizes `sz` at disjoint increasing offsets): from the memory `M` of its bottom, its top
holds a memory with `M`'s allocations and, poisoned below the slots' end, `M`'s area, `M`'s bytes outside the area, and per
parameter the bytes its `Move` read from `M` (`R`), given that each `Move` reads its source in the
memory below it, which is `M` or outside the area, and writes its slot. -/
theorem ecm_moves {T : Frame} {g : Func} {nw : ID → Bool} {b : ID} {M : Mem}
    (hb : rv T b = .mem M) (sz : ABIParam → Nat) (R : ABIParam × ID → Array Byte → Prop) :
    ∀ (n : Nat) {top : ID} {ms : List ID} {sp : List (ABIParam × ID)},
      moveChain g nw n top b = some ms → sp.length = ms.length →
      sp.Pairwise (fun e e' => e.1.offset + (sz e.1 : Int) ≤ e'.1.offset) →
      (∀ e ∈ sp, 0 ≤ e.1.offset ∧ e.1.offset < 2 ^ 24) →
      (∀ e z, (e, z) ∈ sp.zip ms → ∀ mw M0, g.value? z = some mw → rv T mw.args[2]! = .mem M0 →
        ∃ s bs Mz, M0.read s (sz e.1) = some bs ∧ M0.write (ecsSlot e.1.offset.toNat) bs = some Mz ∧
          rv T z = .mem Mz ∧ (mw.args[2]! = b ∨ s.blk ≠ .outargs 0) ∧
          (M.read s (sz e.1) = some bs → R e bs)) →
      ∃ Mt, rv T top = .mem Mt ∧ (∀ blk, (Mt.find? blk).map ecsAttr = (M.find? blk).map ecsAttr) ∧
        (∀ F, (∀ e ∈ sp, e.1.offset.toNat + sz e.1 ≤ F) →
          Mt.poisonBelow (.outargs 0) F = M.poisonBelow (.outargs 0) F) ∧
        (∀ q k, q.blk ≠ .outargs 0 → Mt.read q k = M.read q k) ∧
        ∀ e ∈ sp, ∃ bs, Mt.read (ecsSlot e.1.offset.toNat) (sz e.1) = some bs ∧ R e bs
  | 0, _, _, _, h, _, _, _, _ => by simp [moveChain] at h
  | n + 1, top, ms, sp, h, hlen, hpw, hbd, hF => by
    rcases ecm_step h with ⟨rfl, rfl⟩ | ⟨w, ms', -, hw, -, -, -, hc, rfl⟩
    · have : sp = [] := List.eq_nil_of_length_eq_zero hlen
      subst this
      exact ⟨M, hb, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun e he => absurd he List.not_mem_nil⟩
    have hspne : sp ≠ [] := fun he => by subst he; simp at hlen
    obtain ⟨sp', e, rfl⟩ : ∃ sp' e, sp = sp' ++ [e] :=
      ⟨sp.dropLast, sp.getLast hspne, (List.dropLast_concat_getLast hspne).symm⟩
    have hlen' : sp'.length = ms'.length := by simp at hlen; omega
    have hzip : (sp' ++ [e]).zip (ms' ++ [top]) = sp'.zip ms' ++ [(e, top)] := by
      rw [List.zip_append hlen']; rfl
    rw [hzip] at hF
    obtain ⟨hpw', -, hcross⟩ := List.pairwise_append.1 hpw
    obtain ⟨M0, hM0, hA, hP, hO, hR⟩ := ecm_moves hb sz R n hc hlen' hpw'
      (fun e' he' => hbd e' (List.mem_append_left _ he'))
      (fun e' z hez => hF e' z (List.mem_append_left _ hez))
    obtain ⟨s, bs, Mz, hrd, hW, hz, hcase, hRe⟩ :=
      hF e top (List.mem_append_right _ List.mem_cons_self) w M0 hw hM0
    have hMr : M.read s (sz e.1) = some bs := by
      rcases hcase with hbot | hblk
      · rw [hbot, hb] at hM0; cases hM0; exact hrd
      · rw [← hO s _ hblk]; exact hrd
    have hbe := hbd e (List.mem_append_right _ List.mem_cons_self)
    have hsz := ecs_read_size hrd
    refine ⟨Mz, hz, fun blk => (ecs_find_write hW blk).trans (hA blk), ?_, ?_, ?_⟩
    · intro F hF'
      rw [← hP F fun e' he' => hF' e' (List.mem_append_left _ he')]
      have h1 := hF' e (List.mem_append_right _ List.mem_cons_self)
      refine ecs_poisonBelow_write hW ?_
      simp only [ecsSlot, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), hsz]
      exact h1
    · intro q k hq
      rw [read_write_sep hW (.inr (.inr (.inl hq)))]
      exact hO q k hq
    · intro e' he'
      rcases List.mem_append.1 he' with he' | he'
      · obtain ⟨bs', hr', hR'⟩ := hR e' he'
        refine ⟨bs', ?_, hR'⟩
        rw [read_write_sep hW]
        · exact hr'
        have h1 := hcross e' he' e List.mem_cons_self
        have h2 := hbd e' (List.mem_append_left _ he')
        refine .inr (.inr (.inr (.inl ?_)))
        simp only [ecsSlot, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [List.mem_singleton.1 he']
        refine ⟨bs, ?_, hRe hMr⟩
        rw [← hsz]
        exact GoFV.Proof.Pass.LoadFwd.read_write_self hW

/-! ## Frame variables -/

/-- A pointer-shaped `LocalAddr` evaluates to a pointer outside the outgoing-arguments area. -/
theorem ecm_localAddr_val {env : Env} {tabs : Tables} {g : Func} {T : Frame} {s : ID} {sw : Value}
    {ys : Val} (hsw : g.value? s = some sw) (hid : sw.id = s) (hop : sw.op = .LocalAddr)
    {n : AuxRef} (hax : sw.aux = some n) {e : Option Nat}
    (hsh : shapeOf (typeShapes tabs) g s = .ptr e)
    (hev : evalValue env (Ctx.make tabs g) T sw = .ok ys) :
    ∃ q, ys.asPtrWord = some q ∧ q.blk ≠ .outargs 0 := by
  have hreg : ∀ a ∈ sw.args, Reg T a :=
    evalValue_args_def fun msg h => by rw [hev] at h; cases h
  rw [evalValue_of_regs hreg] at hev
  have he : evalOp env (Ctx.make tabs g) T sw (sw.args.toList.map (rv T))
      ((Ctx.make tabs g).tys[sw.id]?.getD .other) =
      .ok (.ptr ⟨frameBlk tabs (Ctx.make tabs g).act n, 0⟩) := by
    have hf : frameVal (Ctx.make tabs g) sw = some (.ptr ⟨frameBlk tabs (Ctx.make tabs g).act n, 0⟩) := by
      unfold frameVal; rw [hop, hax]; rfl
    unfold evalOp; rw [hop]; dsimp only; rw [hf]; rfl
  rw [he] at hev
  cases hev
  rw [hid, ← shapeOf_eq, hsh]
  refine ⟨_, Ptr.word_asPtrWord (Ptr.inWindow_zero _), ?_⟩
  unfold frameBlk
  split <;> nofun

end GoFV.Proof.EC
