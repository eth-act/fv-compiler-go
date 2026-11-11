import GoFV.Proof.Obj.MemPanic
import GoFV.Proof.Gen.SpecEntry49

variable [GoFV.SSA.Sem.Addrs]

/-!
# The entry stores against a memory related but for their windows (`docs/plans/proofs3.md` §9)

At a function's entry the caller's spill area holds whatever the caller left there: the windows
of the register-assigned parameters (`pendWins`, `GoFV/Gen/Entry49.lean`) are not yet their
blocks' images. The entry relation (`EntryMatch`) therefore relates `runLoc`'s memory to a
machine memory `M` that agrees with the machine's but for a set `W` of bytes, and the entry stores
(`entryStore?`) are run against it: an entry store is a store of G49's frame-variable path
(`entryStore?_spec`; no op of G64's, spill or reload, and no op of G61's group A, so what
`vkind64` accepts of it `vkind60` accepts, `vkind64_eq63`, `vkind63_eq62`, `vkind62_eq61`,
`vkind61_eq60`; no op of G52's–G59's groups and no access off `SP` without an aux, so what
`vkind60` accepts of it `vkind49` accepts, `vkind60_ok49`, in any mode), whose
P0 Prog writes its window in the machine's memory as in `M`. So from
`LocMatch E s b i {m with mem := M}` (`M` agreeing with `m.mem` outside `W` and the store's
window) the Prog runs `m` to `m'` with `LocMatch E s' b (i + 1) {m' with mem := M'}`, `M'`
agreeing with `m'.mem` outside `W` (`g64L_entryStore`): the window is written alike in both
(`writeMem_in`), every other byte is kept (`writeMem_pt`). When the windows of the entry stores
cover `W`, after them `M'` is `m'.mem` and the relation is `LocMatch` (`Whole.lean`,
`sim_entryStores`).

`op_mem2W` is G3's `op_mem2` with the P0 step taken on `m` and the relation on
`{m with mem := M0}`; `g49_storeW` and `g49_stpW` are G49's `g49_store` and `g49_stp` on it.
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64
open GoFV.Proof.Gen

/-! ## Writes of the machine memory -/

/-- Inside its window, `writeMem` does not read the memory. -/
theorem writeMem_in : ∀ (n : Nat) (M1 M2 : Memory) (A : BitVec 64) (V : BitVec (8 * n)) (j : Nat),
    j < n → writeMem M1 A n V (A + BitVec.ofNat 64 j) = writeMem M2 A n V (A + BitVec.ofNat 64 j)
  | 0, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, M1, M2, A, V, 0, _ => by
    simp only [writeMem, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    exact writeMem_pt n _ _ (A + 1) _ A (by simp)
  | n + 1, M1, M2, A, V, j + 1, h => by
    simp only [writeMem]
    rw [← addr_succ]
    exact writeMem_in n _ _ (A + 1) _ j (by omega)

/-- Two memories that agree outside `W` and the window `[A, A + n)` agree, after the same write
of the window, outside `W`. -/
theorem writeMem_agree {M1 M2 : Memory} {A : BitVec 64} {n : Nat} {V : BitVec (8 * n)}
    {W : BitVec 64 → Prop}
    (h : ∀ y, ¬ W y → (∀ j, j < n → y ≠ A + BitVec.ofNat 64 j) → M1 y = M2 y) :
    ∀ y, ¬ W y → writeMem M1 A n V y = writeMem M2 A n V y := by
  intro y hy
  by_cases hin : ∃ j, j < n ∧ y = A + BitVec.ofNat 64 j
  · obtain ⟨j, hj, rfl⟩ := hin
    exact writeMem_in n M1 M2 A V j hj
  · exact writeMem_pt n M1 M2 A V y (h y hy fun j hj he => hin ⟨j, hj, he⟩)

theorem add_ofNat_sub8 (A : BitVec 64) {j : Nat} (h : 8 ≤ j) :
    A + BitVec.ofNat 64 j = A + 8 + BitVec.ofNat 64 (j - 8) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

/-- The same for two writes of 8 bytes at `A` and `A + 8`. -/
theorem writeMem_agree2 {M1 M2 : Memory} {A : BitVec 64} {V1 V2 : BitVec (8 * 8)}
    {W : BitVec 64 → Prop}
    (h : ∀ y, ¬ W y → (∀ j, j < 16 → y ≠ A + BitVec.ofNat 64 j) → M1 y = M2 y) :
    ∀ y, ¬ W y → writeMem (writeMem M1 A 8 V1) (A + 8) 8 V2 y =
      writeMem (writeMem M2 A 8 V1) (A + 8) 8 V2 y := by
  intro y hy
  by_cases hin : ∃ j, j < 16 ∧ y = A + BitVec.ofNat 64 j
  · obtain ⟨j, hj, rfl⟩ := hin
    by_cases h8 : j < 8
    · exact writeMem_pt 8 _ _ _ _ _ (writeMem_in 8 M1 M2 A V1 j h8)
    · rw [add_ofNat_sub8 A (by omega)]
      exact writeMem_in 8 _ _ (A + 8) V2 (j - 8) (by omega)
  · exact writeMem_pt 8 _ _ _ _ _
      (writeMem_pt 8 M1 M2 A V1 y (h y hy fun j hj he => hin ⟨j, hj, he⟩))

/-! ## One store of G49 against a memory related but for some bytes -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}
  {x : AuxRef} {nc : AddrName} {off : Int} {osp : Bool}

/-- G3's `op_mem2` with the P0 step on `m` and the relation on `{m with mem := M0}`: the Prog
writes `Mr` in `m`'s memory, the relation after it is on `{m' with mem := M}`. -/
theorem op_mem2W {P : BitVec 64 → Prop} (F : Facts lc sym text az ez psA.toList ret E)
    {M0 : Memory} (hm : LocMatch E s b i { m with mem := M0 }) (hinv : CoreInv E.ι P K s osp)
    (hkeep : Keeps E P s { m with mem := M0 })
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {pat : Pat} (hone : OneAt2 psA j pat j')
    {mm' : Mem} {M Mr : Memory} (hM : MemInj E.ι mm' M) (hkn : KeysNodup mm')
    (hsep : SepAt osp E.ι P mm') (hP : ∀ y, P y → M y = M0 y) (hKL : KLe K' K)
    (hstep : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m with mem := Mr, pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧ m'.mem = Mr ∧
      m'.x = m.x ∧ LocMatch E { s with mem := .mem mm' } b (i + 1) { m' with mem := M } ∧
      CoreInv E.ι P K' { s with mem := .mem mm' } osp := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hone m
  have hpc : m.pc = E.pcOf b i := hm.pc
  have heta : ({ m with pc := pcAt text psA.toList j } : MState) = m := by rw [← hj, ← hpc]
  rw [heta] at hstar
  obtain ⟨hsl, hfr⟩ := hkeep M hP
  have hlm := locMatch_setMem hm hsl hfr hM (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)), rfl, rfl, hlm,
    (⟨hinv.regs, ⟨mm', rfl, hkn, hsep⟩⟩ : CoreInv E.ι P K { s with mem := .mem mm' } osp).mono
      hKL⟩

/-- `g49_store` from a relation on `{m with mem := M0}`, `M0` agreeing with `m`'s memory outside
`W` and the store's window: the same store, from `m`, to a relation on `{m' with mem := M'}`,
`M'` agreeing with `m'`'s memory outside `W`. -/
theorem g49_storeW (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8) {M0 : Memory}
    (hm : LocMatch E s b i { m with mem := M0 }) (hinv : CoreInv E.ι (StkAt E) K s osp)
    (hsi : SlotInv lc s) (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hι : ∃ a, E.ι (.local lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off))
    {as : As} {n cs : Nat} {rs : Int}
    (hop : storeOp? v.op = some (as, n)) (hsz3 : v.args.size = 3)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hso : argObj lc v 1 = .ok (cs, rs)) (hma : memArg lc v 2 = .ok ())
    (hc : 8 * n ≤ cs ∨ cs = 1 ∧ n = 1)
    (hvs : OneAt2 psA j ⟨plain as (· == regA rs) (slotA · nc off), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s')
    {W : BitVec 64 → Prop}
    (hW : ∀ y, ¬ W y → (∀ j, j < n → y ≠ E.sp + BitVec.ofInt 64
      (frameOff (Link.byId sym text az ez psA.toList) nc off) + BitVec.ofNat 64 j) →
        M0 y = m.mem y) :
    ∃ m' M', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧ m'.x = m.x ∧
      LocMatch E s' b (i + 1) { m' with mem := M' } ∧ CoreInv E.ι (StkAt E) K' s' osp ∧
      SlotInv lc s' ∧ ∀ y, ¬ W y → M' y = m'.mem y := by
  have hl := F.lowered
  have hA := F.addr
  have hnp := storeOp?_ne_phi hop
  have hn := storeOp?_bytes hop
  obtain ⟨sg, hmov⟩ := storeOp?_movMem hop
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hso
  obtain ⟨ks, hks, rfl, hkks⟩ := objOf?_some hor1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkks
  obtain ⟨x', y', p, mm', hx', hy', hsym, hw, rfl⟩ := stepLoc_storeN hl htemp hop
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hy] at hy'
  cases hy'
  rw [symAddr_local hx hvar hf] at hsym
  cases hsym
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  have hcs : 8 * n ≤ cs ∨ cs = 1 := hc.imp_right And.left
  have hbs := (storeBytes_relN hA hn hyv hyf hcs).1
  have hcan : mm.canWrite ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩ n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨a, hpa, haeq⟩ := hι
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inl hcan)
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hk0 hn hpa hyv hyf hcs hw
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0 hw
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by
    have hsp : m.sp = E.sp := hm.frame.1
    rw [hsp, haeq]
  obtain ⟨m', h1, h2, h3, h4, h5⟩ := op_mem2W (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs
    hM' hk' hsep'
    (fun y hy => hout y fun j hj he =>
      hsep0.not_mem hal hpa hy (by simp only [Blk.writableFrom]; omega) (by omega))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun))
    (Mr := writeMem m.mem (a + BitVec.ofInt 64 v.auxInt.toInt) n
      (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))))
    (fun k1 hk1 hok => by
      obtain ⟨has, hf1, -, ht1, -⟩ := plain_spec hok
      simp only [beq_iff_eq] at hf1
      rw [progStep_slotStoreN hks (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf1 ht1
        hnc (by rw [hA']; exact hnil), hA']
      rfl)
  refine ⟨m', _, h1, h3, h4, h5, hsi, ?_⟩
  rw [h2]
  refine writeMem_agree (fun z hz hzw => hW z hz fun j hj he => hzw j hj ?_)
  rw [he, haeq]

/-- `g49_stp` from a relation on `{m with mem := M0}`, as `g49_storeW`. -/
theorem g49_stpW (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8) {M0 : Memory}
    (hm : LocMatch E s b i { m with mem := M0 }) (hinv : CoreInv E.ι (StkAt E) K s osp)
    (hsi : SlotInv lc s) (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hι : ∃ a, E.ι (.local lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off))
    {rx ry : Int} (hop : v.op = .ARM64STP) (hsz4 : v.args.size = 4)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : argObj lc v 1 = .ok (64, rx)) (hyo : argObj lc v 2 = .ok (64, ry))
    (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j ⟨plain .STP (· == pairA rx ry) (slotA · nc off), "STP"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s')
    {W : BitVec 64 → Prop}
    (hW : ∀ y, ¬ W y → (∀ j, j < 16 → y ≠ E.sp + BitVec.ofInt 64
      (frameOff (Link.byId sym text az ez psA.toList) nc off) + BitVec.ofNat 64 j) →
        M0 y = m.mem y) :
    ∃ m' M', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧ m'.x = m.x ∧
      LocMatch E s' b (i + 1) { m' with mem := M' } ∧ CoreInv E.ι (StkAt E) K' s' osp ∧
      SlotInv lc s' ∧ ∀ y, ¬ W y → M' y = m'.mem y := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec hyo
  obtain ⟨kx, hkx, rfl, hkkx⟩ := objOf?_some hor1
  obtain ⟨ky, hky, rfl, hkky⟩ := objOf?_some hor2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkx
  obtain ⟨Z, hZ, hzv, hzf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkky
  obtain ⟨x', y, z, p, q, mm1, mm', -, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_stp hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  rw [pairAddr_local hx hvar hf] at hpq
  cases hpq
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨a, hpa, haeq⟩ := hι
  have hby := (storeBytes_relN hA (n := 8) (by simp) hyv hyf (Or.inl (Nat.le_refl _))).1
  have hbz := (storeBytes_relN hA (n := 8) (by simp) hzv hzf (Or.inl (Nat.le_refl _))).1
  have hcan1 : mm.canWrite ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩ 8 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inl hcan1)
  obtain ⟨hM1, hk1, hback1, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hk0 (by simp) hpa hyv hyf (Or.inl (Nat.le_refl _)) hw1
  have hcan2 : mm1.canWrite ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt + 8⟩ 8 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨hnil', -⟩ := access_nil hM1 hpa (by omega : 0 < 8) (Or.inl hcan2)
  obtain ⟨hM2, hk2, hback2, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 (by simp) hpa hzv hzf (Or.inl (Nat.le_refl _)) hw2
  have hsep1 : SepAt osp E.ι (StkAt E) mm1 := hsep0.write hk0 hw1
  have hsep2 : SepAt osp E.ι (StkAt E) mm' := hsep1.write hk1 hw2
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by
    have hsp : m.sp = E.sp := hm.frame.1
    rw [hsp, haeq]
  have hA8 : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) + 8 =
      a + (BitVec.ofInt 64 v.auxInt.toInt + 8) := by rw [hA', BitVec.add_assoc]
  obtain ⟨m', h1, h2, h3, h4, h5⟩ := op_mem2W (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs
    hM2 hk2 hsep2
    (fun w hw => (hout2 w fun j hj he =>
        hsep1.not_mem hal2 hpa hw (by simp only [Blk.writableFrom]; omega) (by omega)).trans
      (hout1 w fun j hj he =>
        hsep0.not_mem hal1 hpa hw (by simp only [Blk.writableFrom]; omega) (by omega)))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun))
    (Mr := writeMem (writeMem m.mem (a + BitVec.ofInt 64 v.auxInt.toInt) 8
        (BitVec.ofNat (8 * 8) ((m.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8))))
      (a + (BitVec.ofInt 64 v.auxInt.toInt + 8)) 8
        (BitVec.ofNat (8 * 8) ((m.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))))
    (fun k hk hok => by
      obtain ⟨has, hf1, -, ht1, -⟩ := plain_spec hok
      simp only [beq_iff_eq] at hf1
      rw [progStep_slotStp hkx hky (nextAddr_pcAt F.nodup hk) has hf1 ht1 hnc
        (by rw [hA']; exact hnil) (by rw [hA8]; exact hnil'), hA8, hA']
      rfl)
  refine ⟨m', _, h1, h3, h4, h5, hsi, ?_⟩
  rw [h2, ← BitVec.add_assoc]
  refine writeMem_agree2 (fun z hz hzw => hW z hz fun j hj he => hzw j hj ?_)
  rw [he, haeq]

end Cases

/-! ## An entry store of slice G49 -/

/-- The op of an entry store: a store of G3 of `n` bytes, or an `STP` of 16. -/
theorem entryStore?_op {lc : LocCtx} {g : G2In} {v : Value} {off : Int} {n : Nat}
    (h : entryStore? lc g v = some (off, n)) :
    (∃ as, storeOp? v.op = some (as, n)) ∨ (v.op = .ARM64STP ∧ n = 16) := by
  unfold entryStore? at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i as n' hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact .inl ⟨as, hs⟩
      · split at h
        · rename_i hop
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact .inr ⟨by simpa using hop, rfl⟩
        · cases h
    · cases h

/-- An entry store is a load or store the panic theorems know (`memFaultOp`). -/
theorem entryStore?_memFault {lc : LocCtx} {g : G2In} {v : Value} {off : Int} {n : Nat}
    (h : entryStore? lc g v = some (off, n)) : memFaultOp v.op = true := by
  rcases entryStore?_op h with ⟨as, hs⟩ | ⟨hop, -⟩
  · simp [memFaultOp, hs]
  · simp [memFaultOp, hop]

/-- An entry store has an aux (its frame variable). -/
theorem entryStore?_aux {lc : LocCtx} {g : G2In} {v : Value} {off : Int} {n : Nat}
    (h : entryStore? lc g v = some (off, n)) : v.aux ≠ none := by
  intro ha
  unfold entryStore? at h
  split at h
  · cases h
  · rw [frameVar49?_none ha] at h; cases h

/-- **An entry store of slice G64 against a memory related but for some bytes.** From a relation
on `{m with mem := M0}`, `M0` agreeing with `m`'s memory outside `W` and the store's window
(`SP + frameOff` of its `NAME_PARAM` operand, `n` bytes), an entry store (`entryStore?`) that
`checkG64L` accepted runs its Prog from `m` to `m'` (the X registers kept) with a relation on
`{m' with mem := M'}`, `M'` agreeing with `m'`'s memory outside `W`, the class map and G35's
table after the value. -/
theorem g64L_entryStore {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {M0 : Memory} {off : Int} {n : Nat} {W : BitVec 64 → Prop} {osp : Bool}
    (hc : checkG64L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hes : entryStore? lc g v = some (off, n))
    (hm : LocMatch E s bid i { m with mem := M0 })
    (hW : ∀ y, ¬ W y → (∀ j, j < n → y ≠ E.sp + BitVec.ofInt 64 (frameOff L .PARAM off) +
      BitVec.ofNat 64 j) → M0 y = m.mem y)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .ok s') :
    ∃ m' M', PStar H L ps.toList ret m m' ∧ m'.x = m.x ∧
      LocMatch E s' bid (i + 1) { m' with mem := M' } ∧
      G3Inv E lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) ∧ ∀ y, ¬ W y → M' y = m'.mem y := by
  have hmf := entryStore?_memFault hes
  have hcases := memFaultOp_cases hmf
  have hen : entryOp24 v.op = false := by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl
  cases hl0 : lc.ctx.f.lowered with
  | false =>
    rcases nl30_ops (checkNL30_of_64L hl0 hc) hbid hb hi hv hen with h | h | h | h <;>
      rcases hcases with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
      rw [h] at h' <;> cases h'
  | true =>
  have hE0 := hE
  obtain ⟨hE28, hvars⟩ := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE28
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, -, -, -, -⟩ :=
    checkG64L_spec hl0 hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  have h7x : op57a v.op = false ∧ op57b v.op = false ∧ op58a v.op = false ∧ op59p v.op = false := by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
      exact ⟨rfl, rfl, rfl, rfl⟩
  have h5x : op56 v.op = false ∧ op55a v.op = false ∧ op55b v.op = false ∧
      op52b v.op = false ∧ op53a v.op = false ∧ op54a v.op = false := by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hvk, vkind64_eq63 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl),
    vkind63_eq62 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide)
    (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide),
    vkind62_eq61 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide),
    vkind61_eq60 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl)] at hkd
  -- G48's `kind48` takes a call or an access off `SP` without an aux; an entry store has one
  have hkd := (vkind60_ok49 h7x.1 h7x.2.1 h7x.2.2.1 h7x.2.2.2 h5x.1 h5x.2.1 h5x.2.2.1
    h5x.2.2.2.1 h5x.2.2.2.2.1 h5x.2.2.2.2.2 hkd).resolve_right fun ⟨_, hk48⟩ => by
      rcases kind48_cases hk48 with ⟨hc0, -⟩ | ⟨-, ha, -⟩
      · rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hc0 <;>
          cases hc0
      · exact entryStore?_aux hes ha
  obtain ⟨x, hfv, htemp, hVar, hshape⟩ := entryStore?_spec hes hkd
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE0.env.env.env.env.env
  have hR := kread_of_reads hreads
  have hsz := slot_sizes hlcE hcf hinv.slots
  have hι := var49_addr hfv hv hvars
  rw [kAt_succ hi hv, uL35_succ hl hi hv]
  cases hVar with
  | addr hop => rcases hshape with ⟨as, h⟩ | ⟨h, -⟩ <;> rw [hop] at h <;> cases h
  | load hop =>
    rcases hshape with ⟨as, h⟩ | ⟨h, -⟩
    · rcases loadOp?_op hop with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ |
        ⟨h', -⟩ <;> rw [h'] at h <;> cases h
    · rw [h] at hop; cases hop
  | ldp hop => rcases hshape with ⟨as, h⟩ | ⟨h, -⟩ <;> rw [hop] at h <;> cases h
  | store hop hsz3 hmt hhn hso hma hcw =>
    rcases hshape with ⟨as', h⟩ | ⟨h, -⟩
    · rw [hop] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨m', M', h1, h2, h3, h4, h5, h6⟩ := g49_storeW (H := H) F hF hsz hm hinv.core
        hinv.slots hR (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hfv.aux hfv.var hfv.loc
        hfv.cls hι hop hsz3 hmt hhn hso hma hcw hvs htemp hs hW
      refine ⟨m', M', h1, h2, h3, ⟨h4, h5⟩, ?_, h6⟩
      have hops : v.op = .ARM64MOVDstore ∨ v.op = .ARM64MOVBstore ∨ v.op = .ARM64MOVHstore ∨
          v.op = .ARM64MOVWstore := by
        rcases storeOp?_op hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
      have hl0 : loadOp? v.op = none := by
        rcases hops with h | h | h | h <;> rw [h] <;> rfl
      have hue : uEntry c.cx.lc v = none := by
        have : narrowLd? c.cx.lc v = none := by
          unfold narrowLd?; rcases hops with h | h | h | h <;> rw [h] <;> rfl
        unfold uEntry; rw [this]
      rw [uStep35_nil hue (ldEntry35_none hl0)
        (by rcases hops with h | h | h | h <;> simp [pairOp35, h, hfv.aux])
        (by rcases hops with h | h | h | h <;>
          simp [keep34, keep31, keepOp31, keepOp34, h, hfv.aux])
        (by rcases hops with h | h | h | h <;> rw [h] <;> nofun)
        (by rcases hops with h | h | h | h <;> rw [h] <;> nofun)]
      intro e he'
      cases he'
    · rw [h] at hop; cases hop
  | stp hop hsz4 hmt hhn hxo hyo hma =>
    rcases hshape with ⟨as', h⟩ | ⟨-, rfl⟩
    · rw [hop] at h; cases h
    obtain ⟨m', M', h1, h2, h3, h4, h5, h6⟩ := g49_stpW (H := H) F hF hsz hm hinv.core
      hinv.slots hR (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hfv.aux hfv.var hfv.loc
      hfv.cls hι hop hsz4 hmt hhn hxo hyo hma hvs htemp hs hW
    refine ⟨m', M', h1, h2, h3, ⟨h4, h5⟩, ?_, h6⟩
    have hue : uEntry c.cx.lc v = none := by
      have : narrowLd? c.cx.lc v = none := by unfold narrowLd?; rw [hop]; rfl
      unfold uEntry; rw [this]
    rw [uStep35_nil hue (ldEntry35_none (by rw [hop]; rfl)) (by simp [pairOp35, hop])
      (by simp [keep34, keep31, keepOp31, keepOp34, hop]) (by rw [hop]; nofun)
      (by rw [hop]; nofun)]
    intro e he'
    cases he'

end GoFV.Proof.Obj
