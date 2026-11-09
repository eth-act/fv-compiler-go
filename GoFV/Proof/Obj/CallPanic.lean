import GoFV.Proof.Obj.G30

/-!
# Static calls whose callee panics (`docs/plans/proofs3.md` §6, §9)

A static call of slice G30 that panics in `runLoc` (its callee panicked, `callOp`): genssa's
Progs run the no-ops before the `CALL sym(SB)` and the `CALL` (`X30` the return address, the PC the
callee's symbol), where the runtime hook panics with the same panic by the callee contract
`CallPanicOK` (trusted, as `CallOK` for a callee that returns): `g30_callPanic` (`runLoc` →
`runProg` on P0), `g30_obj_callPanic` (→ `runMach` on the linked words, `obj_panic`). A function
with no arm64 op has no call (`nl30_ops`); in one with, `checkG30` is `checkG29`, whose static
calls are G15's (`vk28_vk18`, `vk18_call`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen

/-- **The callee contract for a panic** at the static call `v` from `s`, which panics with `e`: at
every machine state `m₁` at the callee's symbol that is `m` but for `X30`, with the arguments in
their ABI registers `ins` and the memory injected (`CallSpec`'s premises), the runtime hook
panics with `e` (trusted, as `CallOK`). -/
def CallPanicOK (H : Hooks) (E : MatchEnv) (g : G2In) (L : Link) (lc : LocCtx) (s : LocState)
    (v : Value) (m : MState) (e : Panic) : Prop :=
  v.op = .ARM64CALLstatic → ∀ name abi cabi ins outs y (args : List Val) (mm : Mem) (m₁ : MState),
    callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
    callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) → g.syms[y]? = some (name, abi) →
    args.length = v.args.toList.dropLast.length →
    (∀ (j : Nat) (a : ID) (x : Val), v.args.toList.dropLast[j]? = some a → args[j]? = some x →
      s.read lc a = .ok x) →
    s.mem = .mem mm → m₁.pc = L.sym y → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv →
    m₁.mem = m.mem → (∀ k, k ≠ 30 → m₁.x k = m.x k) →
    args.length = ins.length →
    (∀ (j r : Nat) (x : Val), ins[j]? = some r → args[j]? = some x → RegRel E.ι x m₁ r) →
    MemInj E.ι mm m₁.mem → KeysNodup mm → SepFrom E.ι (StkAt E) mm →
    ∃ m', H.call m₁ = some (.panicked e m')

/-- A static call of G18's kinds is `VK15.call`'s. -/
theorem vk18_call {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK18 lc g v kd)
    (hop : v.op = .ARM64CALLstatic) :
    ∃ name abi cabi ins outs, callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) ∧
      callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) ∧ (∀ r ∈ ins ++ outs, r < 16) ∧
      v.args.toList.dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) ∧
      kd = .prog (callPat g name abi) := by
  cases h with
  | stIdx h => rw [hop] at h; cases h
  | g17 h =>
    cases h with
    | getG h => rw [hop] at h; cases h
    | g16 h =>
      cases h with
      | addSh h => rw [hop] at h; cases h
      | g15 h =>
        cases h with
        | g14 hne _ => exact absurd hop hne
        | call _ hcall hcr _ _ _ _ h16 hlen hargs _ _ =>
          exact ⟨_, _, _, _, _, hcall, hcr, h16, hlen, hargs, rfl⟩

/-- A static call of G28's kinds is G18's. -/
theorem vk28_vk18 {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (hVK : VK28 lc g v kd)
    (h : v.op = .ARM64CALLstatic) : VK18 lc g v kd := by
  cases hVK with
  | memEq h' => rw [h] at h'; cases h'
  | g27 _ h27 =>
    cases h27 with
    | logSh h' => rw [h] at h'; cases h'
    | g25 _ h25 =>
      cases h25 with
      | csel h' => rw [h] at h'; cases h'
      | csel0 h' => rw [h] at h'; cases h'
      | tst h' => rw [h] at h'; cases h'
      | tstw h' => rw [h] at h'; cases h'
      | g24 _ _ h24 =>
        cases h24 with
        | sp h' => rw [h] at h'; cases h'
        | g23 _ h23 =>
          cases h23 with
          | cset h' => rw [h] at h'; simp [Cond.ofOp] at h'
          | g22 _ h22 =>
            cases h22 with
            | ldp h' => rw [h] at h'; cases h'
            | stp h' => rw [h] at h'; cases h'
            | g21 _ h21 =>
              cases h21 with
              | regSame h' => rw [h] at h'; cases h'
              | regMov h' => rw [h] at h'; cases h'
              | g20 _ h20 =>
                cases h20 with
                | nop h' => rw [h] at h'; cases h'
                | g19 _ h19 =>
                  cases h19 with
                  | pb h' => rw [h] at h'; cases h'
                  | g18 _ h18 => exact h18

/-- **A static call of slice G30 whose callee panics**: from a `LocMatch`ed P0 state, the Progs
of the call run to the callee's symbol, where the runtime panics with `e` (`CallPanicOK`). -/
theorem g30_callPanic {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic}
    (hc : checkG30 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64CALLstatic) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hok : CallPanicOK H E g L lc s v m e) :
    ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl0 : lc.ctx.f.lowered with
  | false =>
    rcases nl30_ops (checkG30_nl hl0 hc) hbid hb hi hv (by rw [hop]; rfl) with h | h | h | h <;>
      rw [h] at hop <;> cases hop
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG29_spec hl0 (checkG30_lowered hl0 hc)
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
  obtain ⟨-, hVK⟩ := vkind28_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have hR : KRead c.cx.lc v (kAt c.cx.lc kt bid blk i).get := kread_of_reads hreads
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  obtain ⟨name, abi, cabi, ins, outs, hcall', hcr, h16, hlen, hargs, rfl⟩ :=
    vk18_call (vk28_vk18 hVK hop) hop
  -- the machine: no-ops, then the `CALL`
  obtain ⟨k, -, hk', hokp, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, -, -, -, -, -, ht1, ht2, ht3, y, hy1, hy⟩ := callPat_spec hokp
  let m₁ : MState :=
    { m with x := (fun q => if q = 30 then pcAt text c.cx.ps.toList (k + 1) else m.x q),
             pc := (Link.byId sym text az ez c.cx.ps.toList).sym y }
  have hm1x : ∀ q, q ≠ 30 → m₁.x q = m.x q := fun q hq => by
    show (if q = 30 then _ else m.x q) = m.x q
    exact ite_eq_right_iff.2 fun h => absurd h hq
  have hcstep : progStep (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList[k]
      { m with pc := pcAt text c.cx.ps.toList k } = .ok m₁ := by
    rw [progStep_callSym (nextAddr_pcAt F.nodup hk') has ht1 ht2 ht3 hy1, wX_pc]
    simp only [MState.wX, show ¬ ((30 : Reg) = 31) by decide, ↓reduceIte]
    rfl
  -- the arguments, read from their ABI registers
  have hargs' : ∀ a ∈ v.args.toList.dropLast, ∃ x, s.read c.cx.lc a = .ok x ∧
      ∀ r, c.cx.lc.home a = some (.reg r) → RegRel E.ι x m₁ r := by
    intro a ha
    obtain ⟨j0, hj0, rfl⟩ := List.getElem_of_mem ha
    have hjin : j0 < ins.length := hlen ▸ hj0
    have hz : (v.args.toList.dropLast[j0], ins[j0]) ∈ v.args.toList.dropLast.zip ins :=
      List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨List.getElem?_eq_getElem hj0,
        List.getElem?_eq_getElem hjin⟩)
    have hh := hargs _ _ hz
    have hr16 := h16 _ (List.mem_append_left _ (List.getElem_mem hjin))
    have hrz : ins[j0] ≠ zeroReg := by unfold zeroReg; omega
    obtain ⟨c0, hc0⟩ : ∃ c0, cls (c.cx.lc.ty v.args.toList.dropLast[j0]) = some c0 :=
      Option.isSome_iff_exists.1 (F.clsReg _ _ hh hrz)
    obtain ⟨x, hx, hxv, -⟩ := arg_rel hA hl hm hinv.core hh hc0
      (fun hr => hR (by rw [hop]; nofun) _ (List.dropLast_subset _ ha) _ _ hh hr hc0)
      (Or.inr ⟨by omega, objX?_low hr16⟩)
    refine ⟨x, hx, fun r hr => ?_⟩
    rw [hh] at hr
    cases hr
    refine ⟨fun q hq => ?_, fun q hq => by rw [objV?_low (by omega)] at hq; cases hq⟩
    rw [objX?_low hr16] at hq
    cases hq
    rw [rX_lt (by omega)] at hxv
    rw [hm1x _ (reg5_ne30 hr16)]
    exact hxv
  obtain ⟨args, hal, hargsP⟩ := list_choose _ hargs'
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hkn, hsep⟩ := hinv.core.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨m', hcallH⟩ := hok hop name abi cabi ins outs y args mm m₁ hcall' hcr hy hal
    (fun j a x ha hx => (hargsP j a x ha hx).1) hmm rfl rfl rfl rfl rfl hm1x
    (by rw [hal, hlen])
    (fun j r x hr hx => by
      have hjl : j < v.args.toList.dropLast.length := by
        rw [← hal]; exact (List.getElem?_eq_some_iff.1 hx).1
      have ha := List.getElem?_eq_getElem hjl
      exact (hargsP j _ x ha hx).2 r
        (hargs _ _ (List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨ha, hr⟩))))
    hMI hkn hsep
  refine ⟨m₁, hstar.tail (pstep_at F.nodup F.lt F.ret hk' rfl hcstep),
    (hsyms y).1, Or.inr ⟨progAt?_none (hsyms y).2, m', hcallH⟩⟩

/-- **A static call of slice G30 whose callee panics, down to the machine words**: machine steps
of the linked code to a state that panics with `e` (the hook at the callee's symbol,
`MPanics`). -/
theorem g30_obj_callPanic {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64}
    {code : Code} {retM : BitVec 64} {t : MState}
    (hc : checkG30 lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64CALLstatic) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hok : CallPanicOK H E g L lc s v m e)
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e := by
  obtain ⟨m', hp, hpp⟩ := g30_callPanic hc hE hbid hb hi hv hop hm hinv hok
  obtain ⟨t1, ht1, hR1, hI1⟩ := obj_star hO hH hp hR (locMatch_inv hE.env.env.env.env hm) hic
  obtain ⟨t2, ht2, hpan⟩ := obj_panic hO hHP hR1 (hI1.resolve_right hpp.1) hpp
  exact ⟨t2, mstar_trans ht1 ht2, hpan⟩

end GoFV.Proof.Obj
