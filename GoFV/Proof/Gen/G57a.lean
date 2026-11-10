import GoFV.Proof.Gen.G49
import GoFV.Proof.Gen.Spec57a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G57, group A: `STPW`; narrow pair loads of a global or a frame variable
(`docs/plans/proofs3.md` §4)

`vkind57a` (`GoFV/Gen/Check57a.lean`) accepts `STPW` and the `LDPW`/`LDPSW` with an aux; `VK57a`
(`Spec57a.lean`) says what it accepted.

* `STPW (Rx, Ry), off(Rn)` (`g57_stpw`) is G4's `STP` at `n = 4`: `runLoc` runs `stPair 4`
  (`stepLoc_stpw`), the 4-byte stores of `storeBytes 4` (the low word of an integer, `poison`
  bytes of a pointer) at `pairAddr` (`pairAddr_noAuxN`); the machine (`progStep_stpw`) stores the
  low 32 bits of `X kx` at `X kn + off` and of `X ky` 4 bytes above, which `storeBytes_relN`
  relates at `n = 4` for sources of classes of at least 32 bits (`memInj_storeN`).
* `LDPW`/`LDPSW` of a global (`g57_ldpwGlob`) is G50's `LDPW` (`stepLoc_ldPair`, `lo_loadN` at
  `n = 4`) at G22's address of the global's block (`pairAddr_globN`, `G2Env.glob`); of a frame
  variable in a `Blk.temp` block (`g57_ldpwVar`), at G6's address (`pairAddr_varN`, `var_addr`).
  The machine (`step_ldpw57`) loads the 4-byte words at the operand's address (`ctx_mem_glob`,
  `ctx_mem_slot`), zero- or sign-extended.

The pair loads read valid bytes at both addresses by G50's run premise `PairPre50`, which states
it for every `pairOp50` op with or without an aux (it is part of `G54Pre`); `STPW` needs none (a
store `runLoc` runs succeeded). The upper-bit table is empty after each (`uStep35_57a`).
`vk57a_step` is one value, in `vk55_step`'s form (the frame variables' places and the globals'
addresses come from `G49Env`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## `stepLoc` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_four57a {a b c d : ID} :
    [a, b, c, d].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        (s.read lc d).bind fun w => .ok [x, y, z, w] := rfl

/-- `STPW [off] a x y mem`: the 4-byte writes of `x` and `y` at `pairAddr`, in that order, which
succeeded. -/
theorem stepLoc_stpw (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64STPW) {a0 a1 a2 a3 : ID} (ha : v.args = #[a0, a1, a2, a3]) {mm : Mem}
    (hm : s.read lc a3 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y z p q mm1 mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ s.read lc a2 = .ok z ∧
      pairAddr lc.ctx v 4 x = some (p, q) ∧ mm.write p (Arm64.storeBytes 4 y) = some mm1 ∧
      mm1.write q (Arm64.storeBytes 4 z) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1, a2, a3].mapM (s.read lc) = _ at hmap
  rw [mapM_four57a] at hmap
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
    have hev : evalOpL true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
        arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) := by
      unfold evalOpL; rw [hop]; rfl
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, y, z, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      cases hpq : pairAddr lc.ctx v 4 x with
      | none =>
        have he : ∃ m1 m2, arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
            if [x, y, z, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
            else .stuck m2 :=
          ⟨_, _, by unfold arm64Op; rw [hn, hop]; simp only [hpq]; rfl⟩
        obtain ⟨m1, m2, he⟩ := he
        rw [he] at hr
        split at hr <;> cases hr
      | some pq =>
        obtain ⟨p, q⟩ := pq
        have he : ∃ w, arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
            writeRes w (Arm64.storePair 4 p q y z mm) :=
          ⟨_, by unfold arm64Op; rw [hn, hop]; simp only [hpq]; rfl⟩
        obtain ⟨w, he⟩ := he
        rw [he] at hr
        cases hw1 : mm.write p (Arm64.storeBytes 4 y) with
        | none =>
          simp only [Arm64.storePair, hw1, Option.bind_none] at hr
          cases hr
        | some mm1 =>
          cases hw2 : mm1.write q (Arm64.storeBytes 4 z) with
          | none =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
          | some mm' =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
            exact ⟨x, y, z, p, q, mm1, mm', rfl, rfl, rfl, hpq, hw1, hw2, rfl⟩

end Step

/-! ## The addresses -/

/-- The element addresses of a pair access of `n`-byte elements of a global: its block at the
offset and `n` bytes above (G22's `pairAddr_glob` at `n`). -/
theorem pairAddr_globN {ctx : Ctx} {v : Value} {x : AuxRef} {name : GoStr} {abi : Nat} {a : Val}
    {n : Nat} (hx : v.aux = some x) (hs : symOf? ctx.tabs x = some (name, abi)) :
    pairAddr ctx v n a = some (⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt⟩,
      ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n⟩) := by
  unfold pairAddr
  rw [symAddr_global hs hx,
    symAddr_global (v := { v with auxInt := v.auxInt + Int64.ofNat n }) hs hx]
  simp only [Option.bind_some, Option.map_some, ofInt_addN]

/-- The element addresses of a pair access of `n`-byte elements of a frame variable not converted
to an integer: its `temp` block at the offset and `n` bytes above (G6's `pairAddr_var` at `n`). -/
theorem pairAddr_varN {lc : LocCtx} {v : Value} {x : AuxRef} {a : Val} {n : Nat}
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = false) :
    pairAddr lc.ctx v n a = some (⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩,
      ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n⟩) := by
  unfold pairAddr
  rw [symAddr_var hx hvar hf,
    symAddr_var (v := { v with auxInt := v.auxInt + Int64.ofNat n }) hx hvar hf]
  simp only [Option.bind_some, Option.map_some, ofInt_addN]

/-! ## The machine -/

section Progs

/-- `STPW (Rx, Ry)` at the address `A` of its operand: the low words of `X kx` and `X ky`. -/
private theorem eff_stpw57 {c : ProgCtx} {kx ky : Nat} {A : BitVec 64} (hkx : kx < 32)
    (hky : ky < 32) (has : c.p.as = .STPW) (hf : c.p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky))
    (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, 4, (c.s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 4)),
        (A + BitVec.ofNat 64 4, 4, (c.s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 4))] } := by
  have hname : As.name .STPW = "STPW" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_x_r0 hkx, ctx_x_r0 hky]
  rfl

/-- `LDPW`/`LDPSW` at the address `A` of its operand: two 4-byte loads at `A` and 4 bytes above,
sign-extended if `sg` (`Progs50.lean`'s `eff_ldpw`). -/
private theorem eff_ldpw57 {c : ProgCtx} {ka kb : Nat} {A : BitVec 64} {sg : Bool} (hka : ka < 31)
    (hkb : kb < 31) (has : c.p.as = .LDPW ∧ sg = false ∨ c.p.as = .LDPSW ∧ sg = true)
    (hma : c.mem c.p.from_ = .ok (A, none))
    (ht : c.p.to = pairA (REG_R0 + ka) (REG_R0 + kb)) :
    progEffect c = .ok
      { x := [(kb, if sg then ProgOp.sextTo64 4 (c.load (A + BitVec.ofNat 64 4) 4)
                else c.load (A + BitVec.ofNat 64 4) 4),
              (ka, if sg then ProgOp.sextTo64 4 (c.load A 4) else c.load A 4)],
        loads := [(A + BitVec.ofNat 64 4, 4), (A, 4)] } := by
  rcases has with ⟨has, rfl⟩ | ⟨has, rfl⟩
  · have hname : As.name .LDPW = "LDPW" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wX_r0 hka, eff_wX_r0 hkb]
    rfl
  · have hname : As.name .LDPSW = "LDPSW" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wX_r0 hka, eff_wX_r0 hkb]
    rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `STPW (Rx, Ry), off(Rn)`, both addresses outside the nil page: the low 32 bits of `X kx` at
`X kn + off`, then those of `X ky` 4 bytes above. -/
theorem progStep_stpw {kn kx ky : Nat} {off : Int} (hkn : kn < 32) (hkx : kx < 32) (hky : ky < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .STPW)
    (hf : p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky)) (hsc : p.scond = 0)
    (ht : p.to = memA (REG_R0 + kn) off)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false)
    (hnil4 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 4) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 4
          (BitVec.ofNat (8 * 4) ((s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 4))))
        (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 4) 4
          (BitVec.ofNat (8 * 4) ((s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 4))),
      pc := next } := by
  have hma := ctx_mem_reg (c := ⟨L, s, p⟩) hkn hsc (off := off)
  rw [← ht] at hma
  have he := eff_stpw57 (c := ⟨L, s, p⟩) hkx hky has hf hma
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by simp [Eff.nilAccess?, List.find?, hnil, hnil4])]
  rfl

/-- `LDPW`/`LDPSW` at an operand of address `A` (`Ra`, `Rb` not `ZR`), both addresses outside the
nil page: `Ra` from the 4 bytes at `A`, then `Rb` from the 4 bytes above, zero-extended or, if
`sg`, sign-extended. -/
theorem step_ldpw57 {ka kb : Nat} {A : BitVec 64} {sg : Bool} (hka : ka < 31) (hkb : kb < 31)
    (hn : L.nextAddr p.id = some next)
    (has : p.as = .LDPW ∧ sg = false ∨ p.as = .LDPSW ∧ sg = true)
    (hma : (ProgCtx.mk L s p).mem p.from_ = .ok (A, none))
    (ht : p.to = pairA (REG_R0 + ka) (REG_R0 + kb))
    (hnil : nilPage A = false) (hnil4 : nilPage (A + BitVec.ofNat 64 4) = false) :
    progStep L p s = .ok { (s.wX (BitVec.ofNat 5 ka)
        (if sg then ProgOp.sextTo64 4 ((readMem s.mem A 4).setWidth 64)
          else (readMem s.mem A 4).setWidth 64)).wX (BitVec.ofNat 5 kb)
        (if sg then ProgOp.sextTo64 4 ((readMem s.mem (A + BitVec.ofNat 64 4) 4).setWidth 64)
          else (readMem s.mem (A + BitVec.ofNat 64 4) 4).setWidth 64) with
      pc := next } := by
  have he := eff_ldpw57 (c := ⟨L, s, p⟩) hka hkb has hma ht
  have hsk : p.isSkip = false := by
    rcases has with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [Prog.isSkip, h]
  rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil, hnil4])]
  rfl

end Progs

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `STPW (Rx, Ry), off(Rn)`: the low words of `Rx` at the address and of `Ry` 4 bytes above,
outside the frame. -/
theorem g57_stpw (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rn rx ry : Int} {cx cy : Nat} (hop : v.op = .ARM64STPW) (hsz4 : v.args.size = 4)
    (hax : v.aux = none) (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hao : argObj lc v 0 = .ok (64, rn)) (hxo : argObj lc v 1 = .ok (cx, rx))
    (hyo : argObj lc v 2 = .ok (cy, ry)) (hma : memArg lc v 3 = .ok ()) (hcx : 32 ≤ cx)
    (hcy : 32 ≤ cy)
    (hvs : OneAt2 psA j
      (.ofShape { as := .STPW, from_ := pairA rx ry, to := memA rn v.auxInt.toInt }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec hyo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kx, hkx, rfl, hkkx⟩ := objOf?_some hor1
  obtain ⟨ky, hky, rfl, hkky⟩ := objOf?_some hor2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkx
  obtain ⟨Z, hZ, hzv, hzf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkky
  obtain ⟨x, y, z, p, q, mm1, mm', hx, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_stpw hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hX] at hx; cases hx
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨hap, haq⟩ := pairAddr_noAuxN hax hpq
  have hby := (storeBytes_relN hA (n := 4) (by simp) hyv hyf (Or.inl (by omega))).1
  have hbz := (storeBytes_relN hA (n := 4) (by simp) hzv hzf (Or.inl (by omega))).1
  have hcan1 : mm.canWrite p 4 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf hap (by omega : 0 < 4) (Or.inl hcan1)
  obtain ⟨hM1, hk1, hback1, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hk0 (by simp) hpa hyv hyf (Or.inl (by omega)) hw1
  have hcan2 : mm1.canWrite q 4 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨a', hqa, haeq', hnil'⟩ := addr_rel hA hM1 hxv hxf haq (by omega : 0 < 4) (Or.inl hcan2)
  obtain ⟨hM2, hk2, hback2, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 (by simp) hqa hzv hzf (Or.inl (by omega)) hw2
  have hsep1 : SepFrom E.ι (StkAt E) mm1 := by
    intro b2 al a2 hb hι w hw
    obtain ⟨al0, hb0, hs0⟩ := hback1 b2 al hb
    rw [← hs0]; exact hsep0 b2 al0 a2 hb0 hι w hw
  have hsep2 : SepFrom E.ι (StkAt E) mm' := by
    intro b2 al a2 hb hι w hw
    obtain ⟨al0, hb0, hs0⟩ := hback2 b2 al hb
    rw [← hs0]; exact hsep1 b2 al0 a2 hb0 hι w hw
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have haeq4 : a + p.off + BitVec.ofNat 64 4 = a' + q.off := by
    rw [← haeq, BitVec.add_assoc]; exact haeq'
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM2 hk2 hsep2
    (fun w hw => (hout2 w fun j hj he => hsep1 _ _ _ hal2 hqa w hw ⟨by omega, by omega⟩).trans
      (hout1 w fun j hj he => hsep0 _ _ _ hal1 hpa w hw ⟨by omega, by omega⟩))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
  have haeq0 : ({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kn) +
      BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
  rw [progStep_stpw hkn hkx hky (nextAddr_pcAt F.nodup hk) has hf hsc ht'
    (by rw [haeq0]; exact hnil) (by rw [haeq0, haeq4]; exact hnil'), haeq0, haeq4]
  rfl

/-- `LDPW`/`LDPSW sym+off(SB), (Ra, Rb)`: the two 4-byte words of the global at the offset, at
the global's injected address, zero- or sign-extended. -/
theorem g57_ldpwGlob (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    {ra rb : Nat} {t0 t1 : Ty} {c0 c1 : Nat}
    (hK : KLe K' (kSet (kSet K ra (some c0)) rb (some c1))) (hpre : PairPre50 lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {sg : Bool} {x : AuxRef} {name : GoStr} {abi : Nat} (hop : LdpwOp v.op as sg)
    (hsz2 : v.args.size = 2) (hx : v.aux = some x)
    (hsy : symOf? lc.ctx.tabs x = some (name, abi))
    {oa ob : Int} (hty : lc.ty v.id = .tuple [t0, t1]) (h0 : cls t0 = some c0)
    (h1 : cls t1 = some c1) (h80 : 8 ≤ c0) (h81 : 8 ≤ c1) (hma : memArg lc v 1 = .ok ())
    (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hza : ra ≠ zeroReg) (hzb : rb ≠ zeroReg) (hda : destOK ra = true) (hdb : destOK rb = true)
    (hoa : objOf? ra = some oa) (hob : objOf? rb = some ob)
    (hvs : OneAt2 psA j
      ⟨plain as (globA g name abi v.auxInt.toInt) (· == pairA oa ob), "LDPW sym(SB)"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧
      WPairW ra rb sg m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hpo := hop.pairOp
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ka, hka, rfl, hkka⟩ := objOf?_some hoa
  obtain ⟨kb, hkb, rfl, hkkb⟩ := objOf?_some hob
  have hka' : ka < 31 := by
    rcases hkka with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hza
    · exact h
  have hkb' : kb < 31 := by
    rcases hkkb with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hzb
    · exact h
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, rfl⟩ :=
    stepLoc_ldPair hl htemp hpo (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, q, mm2, bs, bs', hpq, hmm2, hrp, hrq, -⟩ := hpre as 4 sg false hpo a0 y ha0 hy
  rw [hmm] at hmm2
  cases hmm2
  rw [pairAddr_globN hx hsy] at hpq
  cases hpq
  rw [pairAddr_globN hx hsy]
  simp only [Option.elim]
  rw [hty, loadPair_tupleN (by decide), retypeL_pair,
    write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, hf1, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht'
  obtain ⟨g1, g2, -, -, g5, yy, hy1, hyy⟩ := globA_eq hf1
  have hpa := hglob yy name abi hyy
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < 4) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨hnil', -⟩ := access_nil hMI hpa (by omega : 0 < 4) (Or.inr (by rw [hrq]; rfl))
  have ht0 := cls_ne_bool h0 h80
  have ht1 := cls_ne_bool h1 h81
  have hrel0 := valRel_retypeL_lo hA h0 ht0
    ((lo_loadN (sg := sg) hA hMI (by simp) (fun h => absurd h (by decide)) ht0 hpa hrp).mono
      (cls_le h0))
  have hrel1 := valRel_retypeL_lo hA h1 ht1
    ((lo_loadN (sg := sg) hA hMI (by simp) (fun h => absurd h (by decide)) ht1 hpa hrq).mono
      (cls_le h1))
  obtain ⟨hlm1, hinv1⟩ := finish_reg hm hinv hda (by omega : ka < 32) hoa hrel0
    (fits_retypeL h0 _) (b' := b) (i' := i + 1)
  obtain ⟨hlm2, hinv2⟩ := finish_reg hlm1 hinv1 hdb (by omega : kb < 32) hob hrel1
    (fits_retypeL h1 _) (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2, hinv2.mono hK, hsi,
    ka, kb, _, _, hoa, hob, by simp only [wX_pc] <;> rfl⟩
  have has' : psA.toList[k].as = .LDPW ∧ sg = false ∨ psA.toList[k].as = .LDPSW ∧ sg = true := by
    rw [has]; rcases hop with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
  have hA4 : sym yy + BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 4 =
      sym yy + (BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 4) := BitVec.add_assoc _ _ _
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].from_ =
      .ok (sym yy + BitVec.ofInt 64 v.auxInt.toInt, none) := ctx_mem_glob g1 g2 g5 hy1
  rw [step_ldpw57 hka' hkb' (nextAddr_pcAt F.nodup hk) has' hma' ht' hnil
    (by rw [hA4]; exact hnil'), hA4]
  simp only [wX_pc]

/-- `LDPW`/`LDPSW off'(RSP), (Ra, Rb)`: the two 4-byte words of a frame variable in a `Blk.temp`
block at the offset, at its injected address `SP + frameOff off`, zero- or sign-extended. -/
theorem g57_ldpwVar (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    {ra rb : Nat} {t0 t1 : Ty} {c0 c1 : Nat}
    (hK : KLe K' (kSet (kSet K ra (some c0)) rb (some c1))) (hpre : PairPre50 lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {sg : Bool} {x : AuxRef} {off : Int} (hop : LdpwOp v.op as sg)
    (hsz2 : v.args.size = 2) (hx : v.aux = some x) (hvar : isVar lc x = true)
    (hf : lc.ctx.tabs.forgeable x = false)
    (hι : ∃ a, E.ι (.temp lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off))
    {oa ob : Int} (hty : lc.ty v.id = .tuple [t0, t1]) (h0 : cls t0 = some c0)
    (h1 : cls t1 = some c1) (h80 : 8 ≤ c0) (h81 : 8 ≤ c1) (hma : memArg lc v 1 = .ok ())
    (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hza : ra ≠ zeroReg) (hzb : rb ≠ zeroReg) (hda : destOK ra = true) (hdb : destOK rb = true)
    (hoa : objOf? ra = some oa) (hob : objOf? rb = some ob)
    (hvs : OneAt2 psA j ⟨plain as (slotA · .AUTO off) (· == pairA oa ob), "LDPW var"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧
      WPairW ra rb sg m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hpo := hop.pairOp
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ka, hka, rfl, hkka⟩ := objOf?_some hoa
  obtain ⟨kb, hkb, rfl, hkkb⟩ := objOf?_some hob
  have hka' : ka < 31 := by
    rcases hkka with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hza
    · exact h
  have hkb' : kb < 31 := by
    rcases hkkb with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hzb
    · exact h
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, rfl⟩ :=
    stepLoc_ldPair hl htemp hpo (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, q, mm2, bs, bs', hpq, hmm2, hrp, hrq, -⟩ := hpre as 4 sg false hpo a0 y ha0 hy
  rw [hmm] at hmm2
  cases hmm2
  rw [pairAddr_varN hx hvar hf] at hpq
  cases hpq
  rw [pairAddr_varN hx hvar hf]
  simp only [Option.elim]
  rw [hty, loadPair_tupleN (by decide), retypeL_pair,
    write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  obtain ⟨a, hpa, haeq⟩ := hι
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < 4) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨hnil', -⟩ := access_nil hMI hpa (by omega : 0 < 4) (Or.inr (by rw [hrq]; rfl))
  have ht0 := cls_ne_bool h0 h80
  have ht1 := cls_ne_bool h1 h81
  have hrel0 := valRel_retypeL_lo hA h0 ht0
    ((lo_loadN (sg := sg) hA hMI (by simp) (fun h => absurd h (by decide)) ht0 hpa hrp).mono
      (cls_le h0))
  have hrel1 := valRel_retypeL_lo hA h1 ht1
    ((lo_loadN (sg := sg) hA hMI (by simp) (fun h => absurd h (by decide)) ht1 hpa hrq).mono
      (cls_le h1))
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hlm1, hinv1⟩ := finish_reg hm hinv hda (by omega : ka < 32) hoa hrel0
    (fits_retypeL h0 _) (b' := b) (i' := i + 1)
  obtain ⟨hlm2, hinv2⟩ := finish_reg hlm1 hinv1 hdb (by omega : kb < 32) hob hrel1
    (fits_retypeL h1 _) (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2, hinv2.mono hK, hsi,
    ka, kb, _, _, hoa, hob, by simp only [wX_pc] <;> rfl⟩
  obtain ⟨has, hf1, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht'
  have has' : psA.toList[k].as = .LDPW ∧ sg = false ∨ psA.toList[k].as = .LDPSW ∧ sg = true := by
    rw [has]; rcases hop with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  have hA4 : a + BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 4 =
      a + (BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 4) := BitVec.add_assoc _ _ _
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].from_ =
      .ok (a + BitVec.ofInt 64 v.auxInt.toInt, none) := by
    rw [← hA']; exact ctx_mem_slot hf1 (.inl rfl)
  rw [step_ldpw57 hka' hkb' (nextAddr_pcAt F.nodup hk) has' hma' ht' hnil
    (by rw [hA4]; exact hnil'), hA4]
  simp only [wX_pc]

end Cases

/-! ## The theorem -/

/-- One value of G57's group A: it runs its one Prog and keeps the activation (`G49Env`), the
match and `G3Inv`, and empties the upper-bit table. The pair loads take G50's `PairPre50`. -/
theorem vk57a_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hcf : checkFrame lc g = .ok ())
    (hv : lc.ctx.f.value? id = some v) (hVK : VK57a lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hL : UOKL m L)
    (hpre : PairPre50 lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
      UOKL m' (uStep35 lc L v) := by
  have hE2 := hE.env.env.env.env.env
  have hvars := hE.env.env.env.env.vars
  have hR := kread_of_reads hreads
  have same : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kStep lc K v).get s' ∧
      SlotInv lc s' → UOKL m' (uStep35 lc L v) →
      ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
        UOKL m' (uStep35 lc L v) :=
    fun m' ⟨h1, h2, h3, h4⟩ hu => ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, hu⟩
  cases hVK with
  | stpw hop hsz4 hax hmt hhn hao hxo hyo hma hcx hcy =>
    have hsz := slot_sizes hE2.lcEq hcf hinv.slots
    obtain ⟨m', h⟩ := g57_stpw (H := H) F hE2.frame hsz hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz4 hax hmt hhn hao hxo hyo hma
      hcx hcy hvs htemp hs
    refine same m' h ?_
    rw [uStep35_57a hop]
    exact fun e he => by cases he
  | glob hop hsz2 hx hsy hty h0 h1 h80 h81 hma hh hne hza hzb hda hdb hoa hob =>
    have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g57_ldpwGlob (H := H) F hE2.glob hm hinv.core hinv.slots
      (kpair_kStep hnp hh hty h0 h1 hne) hpre hj hj' hop hsz2 hx hsy hty h0 h1 h80 h81 hma hh
      hza hzb hda hdb hoa hob hvs htemp hs
    refine same m' ⟨h1, h2, h3, h4⟩ ?_
    rw [uStep35_ldpX hop.pairOp]
    simp only [homeRegs, hh]
    exact uokl_wpair hL hne h5
  | var hop hsz2 hfv hty h0 h1 h80 h81 hma hh hne hza hzb hda hdb hoa hob =>
    have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g57_ldpwVar (H := H) F hm hinv.core hinv.slots
      (kpair_kStep hnp hh hty h0 h1 hne) hpre hj hj' hop hsz2 hfv.aux hfv.var hfv.temp
      (var_addr hfv hv hvars) hty h0 h1 h80 h81 hma hh hza hzb hda hdb hoa hob hvs htemp hs
    refine same m' ⟨h1, h2, h3, h4⟩ ?_
    rw [uStep35_ldpX hop.pairOp]
    simp only [homeRegs, hh]
    exact uokl_wpair hL hne h5

end GoFV.Proof.Gen
