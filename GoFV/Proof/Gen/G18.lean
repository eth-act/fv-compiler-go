import GoFV.Proof.Gen.G17
import GoFV.Proof.Gen.Spec18

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G18: register-index stores (`docs/plans/proofs3.md` §4)

`g18_value`, `g18_term`, `g18_nilPanic`: `g17_value`'s, `g17_term`'s and `g17_nilPanic`'s
statements over `checkG18`, with the same premises.

`MOV{D,W,H,B}storeidx{,2,4,8} ptr idx val mem` runs under `runLoc` as `arm64Op`'s `stIdx`
(`stepLoc_storeIdx`): the `n`-byte store of `val` at the address of G14's `idxSum` (`ADD` of `ptr`
and `idx · 2^sh`), `stuck` when there is none or the write is invalid, so a successful step wrote
valid bytes and needs no premise (as G3's stores). Genssa emits one store to `(Rp)(Ri<<sh)`, whose
address is `X[p] + (X[i] <<< sh)` (`ctx_mem_idx`); the sum is related to that word (`lo_idxSum`),
so the write's address is the injected address of its bytes, outside the nil page (`addr_rel`),
and the machine's store keeps `MemInj` as G3's (`memInj_storeN`, `g18_stIdx`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The opcodes -/

theorem storeIdxOp?_op {op : Op} {as : As} {n sh : Nat} (h : storeIdxOp? op = some (as, n, sh)) :
    (op = .ARM64MOVDstoreidx ∧ as = .MOVD ∧ n = 8 ∧ sh = 0) ∨
    (op = .ARM64MOVWstoreidx ∧ as = .MOVW ∧ n = 4 ∧ sh = 0) ∨
    (op = .ARM64MOVHstoreidx ∧ as = .MOVH ∧ n = 2 ∧ sh = 0) ∨
    (op = .ARM64MOVBstoreidx ∧ as = .MOVB ∧ n = 1 ∧ sh = 0) ∨
    (op = .ARM64MOVHstoreidx2 ∧ as = .MOVH ∧ n = 2 ∧ sh = 1) ∨
    (op = .ARM64MOVWstoreidx4 ∧ as = .MOVW ∧ n = 4 ∧ sh = 2) ∨
    (op = .ARM64MOVDstoreidx8 ∧ as = .MOVD ∧ n = 8 ∧ sh = 3) := by
  unfold storeIdxOp? at h
  split at h <;> first | (cases h; simp) | cases h

/-- A register-index store is no `Phi`, writes `n ∈ {1, 2, 4, 8}` bytes with a shift below 4, and
its opcode is a `movMem` store of `n` bytes. -/
theorem storeIdxOp?_facts {op : Op} {as : As} {n sh : Nat}
    (h : storeIdxOp? op = some (as, n, sh)) :
    op ≠ .Phi ∧ (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) ∧ sh < 4 ∧
      ∃ sg, ProgOp.movMem as.name = some (n, sg, false) := by
  rcases storeIdxOp?_op h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  exact ⟨nofun, by decide, by decide, _, rfl⟩

/-! ## `stepLoc` of a register-index store -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_four {a b c d : ID} :
    [a, b, c, d].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        (s.read lc d).bind fun w => .ok [x, y, z, w] := rfl

/-- A store whose `arm64Op` is `stIdx n scale`: the `n`-byte store at `idxSum scale`. -/
private theorem storeIdx_core {n scale : Nat} (hl : lc.ctx.f.lowered = true)
    (ht : (lc.temps[v.id]?).join = none) (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg)
    (h2 : v.op ≠ .StoreReg) (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (hev : ∀ argv, evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      arm64Op true env lc.ctx s.fr v argv (lc.ty v.id))
    (hst : ∀ x y z mm, nilFaults true lc.ctx v [x, y, z, .mem mm] = none → ∃ w m1 m2,
      arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
        match Arm64.addr (idxSum scale x y) 0 with
        | some p => writeRes w (Arm64.storeN n p z mm)
        | none =>
          if [x, y, z, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
          else .stuck m2)
    {a0 a1 a2 a3 : ID} (ha : v.args = #[a0, a1, a2, a3]) {mm : Mem}
    (hm : s.read lc a3 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y z p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ s.read lc a2 = .ok z ∧
      Arm64.addr (idxSum scale x y) 0 = some p ∧ mm.write p (Arm64.storeBytes n z) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht hne h1 h2 h3 h4 hc hc0 hc1 hf h
  rw [ha] at hmap
  change [a0, a1, a2, a3].mapM (s.read lc) = _ at hmap
  rw [mapM_four] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
  cases hy : s.read lc a1 with
  | panic e m => rw [hx, hy] at hmap; cases hmap
  | stuck msg => rw [hx, hy] at hmap; cases hmap
  | ok y =>
  cases hz : s.read lc a2 with
  | panic e m => rw [hx, hy, hz] at hmap; cases hmap
  | stuck msg => rw [hx, hy, hz] at hmap; cases hmap
  | ok z =>
    rw [hx, hy, hz, hm] at hmap; cases hmap
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, y, z, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      obtain ⟨w, m1, m2, he⟩ := hst x y z mm hn
      cases hp : Arm64.addr (idxSum scale x y) 0 with
      | none =>
        rw [hp] at he; rw [he] at hr
        dsimp only at hr
        split at hr <;> cases hr
      | some p =>
        rw [hp] at he; rw [he] at hr
        change writeRes _ (mm.write p (Arm64.storeBytes n z)) = _ at hr
        cases hw : mm.write p (Arm64.storeBytes n z) with
        | none => rw [hw] at hr; cases hr
        | some mm' =>
          rw [hw] at hr; cases hr
          exact ⟨x, y, z, p, mm', rfl, rfl, rfl, hp, hw, rfl⟩

/-- A register-index store: the `n`-byte store of `val` at the address of `idxSum (2^sh)`, which
succeeded. -/
theorem stepLoc_storeIdx (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {as : As} {n sh : Nat} (hop : storeIdxOp? v.op = some (as, n, sh))
    {a0 a1 a2 a3 : ID} (ha : v.args = #[a0, a1, a2, a3]) {mm : Mem}
    (hm : s.read lc a3 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y z p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ s.read lc a2 = .ok z ∧
      Arm64.addr (idxSum (2 ^ sh) x y) 0 = some p ∧ mm.write p (Arm64.storeBytes n z) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  rcases storeIdxOp?_op hop with ⟨ho, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl⟩ |
    ⟨ho, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl⟩ <;>
  exact storeIdx_core hl ht (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
    (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl)
    (by rw [ho]; rfl) (fun _ => by unfold evalOpL; rw [ho]; rfl)
    (fun _ _ _ _ hn => ⟨_, _, _, by unfold arm64Op; rw [hn, ho]; rfl⟩) ha hm h

end Step

/-! ## The value -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A register-index store `MOV… Rs, (Rp)(Ri<<sh)` of `n` bytes. -/
theorem g18_stIdx (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n sh cs : Nat} {rn ri rs : Int}
    (hop : storeIdxOp? v.op = some (as, n, sh)) (hsz4 : v.args.size = 4)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hao : argObj lc v 0 = .ok (64, rn)) (hio : argObj lc v 1 = .ok (64, ri))
    (hso : argObj lc v 2 = .ok (cs, rs)) (hma : memArg lc v 3 = .ok ())
    (hc : 8 * n ≤ cs ∨ cs = 1 ∧ n = 1)
    (hvs : OneAt2 psA j ⟨plain as (· == regA rs) (· == idxA rn ri sh), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, hn, hsh, sg, hmov⟩ := storeIdxOp?_facts hop
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hio
  obtain ⟨ki, hki, rfl, hkki⟩ := objOf?_some hor1
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec hso
  obtain ⟨ks, hks, rfl, hkks⟩ := objOf?_some hor2
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, y, z, p, mm', hx, hy, hz, hpa, hw, rfl⟩ := stepLoc_storeIdx hl htemp hop
    (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkki
  rw [hy] at hY
  cases hY
  obtain ⟨Z, hZ, hzv, hzf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkks
  rw [hz] at hZ
  cases hZ
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  have hcs : 8 * n ≤ cs ∨ cs = 1 := hc.imp_right And.left
  have hbs := (storeBytes_relN hA hn hzv hzf hcs).1
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨hsv, hsf⟩ := lo64_rel (lo_idxSum hA hxv hyv hxf hyf sh) hpa
  obtain ⟨a, hpa', haeq, hnil⟩ := addr_rel hA hMI hsv hsf hpa (by omega : 0 < n) (Or.inl hcan)
  have haeq' : m.rX (BitVec.ofNat 5 kn) + m.rX (BitVec.ofNat 5 ki) <<< sh = a + p.off := by
    simpa using haeq
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hk0 hn hpa' hzv hzf hcs hw
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0 hw
  have hwf := write_wf hw (by rw [hbs]; omega)
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk' hsep'
    (fun y hy => hout y fun j hj he => hsep0.not_mem hal hpa' hy (by omega) (by omega))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k0 hk0 hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, -, ht', -, -, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf ht'
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].to =
      .ok (a + p.off, none) := by
    rw [ht', ctx_mem_idx hkn hki (by omega)]
    exact congrArg (fun z => Except.ok (z, none)) haeq'
  rw [progStep_storeAt hks (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov) hf
    (by rw [ht']; rfl) hma' hnil]
  rfl

end Cases

/-! ## The theorems -/

/-- One value of G18's kinds (`VK18`) emitted at the Progs from `j` to `j'`: `vk17_step`'s
statement for G18's values, under the same premises. -/
theorem vk18_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK18 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp := by
  cases hVK with
  | g17 hVK17 =>
    exact vk17_step hE F hhome hcf hv hVK17 hvs htemp hj hj' hreads hm hinv hpre hcall hcallz
      hicall hwb hclo hgetg hs
  | stIdx hop hsz4 hmt hhn hao hio hso hma hc =>
    obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE.env.env.env
    have hsz := slot_sizes hlcE hcf hinv.slots
    obtain ⟨m', h1, h2, h3, h4⟩ := g18_stIdx (H := H) F hF hsz hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz4 hmt hhn
      hao hio hso hma hc hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩⟩

/-- **G18, values.** `g17_value`'s statement over `checkG18`, with the same premises. -/
theorem g18_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG18 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks⟩ := checkG18_spec hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨htemp, hVK⟩ := vkind18_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk18_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hcallz hicall
    hwb hclo hgetg hs

/-- A nil check of G18's kinds is G7's. -/
theorem vk18_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK18 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g17 h => exact vk17_nil h hop
  | stIdx hop' => rw [hop] at hop'; cases hop'

/-- **G18, nil panics.** `g17_nilPanic`'s statement over `checkG18`. -/
theorem g18_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG18 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG18_spec hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨-, hVK⟩ := vkind18_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk18_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G18, terminators.** `g17_term`'s statement over `checkG18`. -/
theorem g18_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG18 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG18_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
