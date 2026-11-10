import GoFV.Proof.Gen.G50
import GoFV.Proof.Gen.Spec52b

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G52, group B: `MOD`, `UMOD`, `MODW`, `UMODW` (`docs/plans/proofs3.md` §4)

`vkind52b` (`GoFV/Gen/Check52b.lean`) accepts the remainders; `VK52b` (`Spec52b.lean`) says what it
accepted. `runLoc` runs each as `Arm64.evalPure` on its arguments (`stepLoc_rem52b`): `MOD`/`UMOD`
are `op2` of `srem`/`urem` on the 64-bit registers, `MODW`/`UMODW` `op2w` of them on the low words,
zero-extended (`res32`). As for G37's divides, on 64-bit arguments a register is the machine word,
and on arguments of at least 32 bits its low word is the machine's (`lo_rem52b`), so the result is
the machine's `REM`/`UREM Rm, Rn, Rd` (`sized` at 64 bits) or `REMW`/`UREMW` (`sized` at 32 bits,
the `W` suffix of `baseOf`) (`remF52b`, `progStep_rem52b`). A register without an integer form
gives Phase 1 `poison`, which any machine word refines: no run premise. None of these ops is in an
upper-bit keep or entry table: after each the table is empty (`uStep35_52b`). `vk52b_step` is one
value.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The ops -/

/-- The machine word function of a remainder of G52's group B (`op Rm, Rn, Rd`, `Rn` first). -/
def remF52b : As → BitVec 64 → BitVec 64 → BitVec 64
  | .REM => GoFV.SSA.Sem.Arm64.srem
  | .UREM => GoFV.SSA.Sem.Arm64.urem
  | .REMW => fun x y => (GoFV.SSA.Sem.Arm64.srem (x.setWidth 32) (y.setWidth 32)).setWidth 64
  | _ => fun x y => (GoFV.SSA.Sem.Arm64.urem (x.setWidth 32) (y.setWidth 32)).setWidth 64

theorem rem52b?_some {op : Op} {as : As} {cw : Nat} (h : rem52b? op = some (as, cw)) :
    op = .ARM64MOD ∧ as = .REM ∧ cw = 64 ∨ op = .ARM64UMOD ∧ as = .UREM ∧ cw = 64 ∨
      op = .ARM64MODW ∧ as = .REMW ∧ cw = 32 ∨ op = .ARM64UMODW ∧ as = .UREMW ∧ cw = 32 := by
  unfold rem52b? at h
  split at h <;> (try cases h) <;> simp

/-- After a value of G52's group B the upper-bit table is empty. -/
private theorem uStep35_52b {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} {as : As}
    {cw : Nat} (hop : rem52b? v.op = some (as, cw)) : uStep35 lc L v = [] := by
  rcases rem52b?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The remainders: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_rem52b {as : As} {cw : Nat} (hl : lc.ctx.f.lowered = true)
    (ht : (lc.temps[v.id]?).join = none) (hop : rem52b? v.op = some (as, cw))
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  rcases rem52b?_some hop with ⟨hop, -⟩ | ⟨hop, -⟩ | ⟨hop, -⟩ | ⟨hop, -⟩ <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

end Steps

/-! ## The machine -/

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

private theorem nREM : As.REM.name = "REM" := rfl
private theorem nUREM : As.UREM.name = "UREM" := rfl
private theorem nREMW : As.REMW.name = "REMW" := rfl
private theorem nUREMW : As.UREMW.name = "UREMW" := rfl
private theorem cREMW : ProgOp.chopS "REMW" 1 = "REM" := by decide
private theorem cUREMW : ProgOp.chopS "UREMW" 1 = "UREM" := by decide

/-- `op Rm, Rn, Rd` for a remainder of G52's group B. -/
theorem progStep_rem52b {as : As} {kn km kd : Nat}
    (has : as = .REM ∨ as = .UREM ∨ as = .REMW ∨ as = .UREMW)
    (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (remF52b as (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km))) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (remF52b as (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)))) := by
    rcases has with rfl | rfl | rfl | rfl <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nREM, nUREM, nREMW, nUREMW, hf, ht, hrn, regA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ProgOp.endsS, cREMW, cUREMW,
        ctx_src_reg hkn, ctx_src_reg hkm, ctx_src_reg32 hkn, ctx_src_reg32 hkm]
      simp only [bind, Except.bind, eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, ProgOp.binOp,
        remF52b, sized, trunc_false_setWidth] <;> rfl
  have hsk : p.isSkip = false := by
    rcases has with rfl | rfl | rfl | rfl <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

end Progs

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem res_int52b {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

private theorem low_le52b {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem fits_le52b {c : Nat} {x : Val} {r : BitVec 64} (hf : Fits c x)
    (hr : Arm64.reg x = some r) : c ≤ 64 := by
  cases x with
  | int w v => have : w.bits = c := hf; subst this; cases w <;> decide
  | bool b => have : c = 1 := hf; omega
  | ptr p => have : c = 64 := hf; omega
  | _ => cases hr

/-- The register of an argument of 64 bits is the machine word. -/
private theorem reg64_52b (hA : AddrAgree ι) {x : Val} {X a : BitVec 64} {cx : Nat}
    (hx : ValRel ι x X) (hfx : Fits cx x) (hcx : 64 ≤ cx) (hr : Arm64.reg x = some a) : a = X := by
  have h64 := fits_le52b hfx hr
  have : cx = 64 := by omega
  subst this
  simpa only [BitVec.setWidth_eq] using reg_low hA hx hfx hr

/-- The low word of an argument of at least 32 bits is the machine word's. -/
private theorem reg32_52b (hA : AddrAgree ι) {x : Val} {X : BitVec 64} {a : BitVec 32} {cx : Nat}
    (hx : ValRel ι x X) (hfx : Fits cx x) (hcx : 32 ≤ cx) (hr : Arm64.reg32 x = some a) :
    a = X.setWidth 32 := by
  unfold Arm64.reg32 at hr
  cases hr' : Arm64.reg x with
  | none => rw [hr'] at hr; cases hr
  | some b =>
    rw [hr'] at hr
    cases hr
    exact low_le52b (reg_low hA hx hfx hr') hcx

/-- A remainder of G52's group B on two arguments of at least `cw` bits (`rem52b?`): the
machine's word (`remF52b`). -/
theorem lo_rem52b (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef}
    {as : As} {cw cx cy : Nat} {x y : Val} {X Y : BitVec 64}
    (hop : rem52b? op = some (as, cw)) (hx : ValRel ι x X) (hy : ValRel ι y Y)
    (hfx : Fits cx x) (hfy : Fits cy y) (hcx : cw ≤ cx) (hcy : cw ≤ cy) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure op t k aux [x, y]) (remF52b as X Y) := by
  rcases rem52b?_some hop with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  all_goals first
    | (show Lo ι 64 (Arm64.op2 t _ [x, y]) _
       simp only [Arm64.op2]
       cases hrx : Arm64.reg x with
       | none => trivial
       | some a =>
         cases hry : Arm64.reg y with
         | none => trivial
         | some b =>
           rw [reg64_52b hA hx hfx hcx hrx, reg64_52b hA hy hfy hcy hry]
           show Lo ι 64 (Arm64.res t _) _
           rw [res_int52b ht]
           rfl)
    | (show Lo ι 64 (Arm64.op2w t _ [x, y]) _
       simp only [Arm64.op2w]
       cases hrx : Arm64.reg32 x with
       | none => trivial
       | some a =>
         cases hry : Arm64.reg32 y with
         | none => trivial
         | some b =>
           rw [reg32_52b hA hx hfx hcx hrx, reg32_52b hA hy hfy hcy hry]
           show Lo ι 64 (Arm64.res t _) _
           rw [res_int52b ht]
           rfl)

end Vals

/-! ## The case -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `op Rm, Rn, Rd` for a remainder of G52's group B. -/
theorem g52b_rem (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {cw cx cy c : Nat} {rn rm rd : Int}
    (hop : rem52b? v.op = some (as, cw))
    (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (cx, rn)) (hbo : argObj lc v 1 = .ok (cy, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hcx : cw ≤ cx) (hcy : cw ≤ cy)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by
    rcases rem52b?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  have has : as = .REM ∨ as = .UREM ∨ as = .REMW ∨ as = .UREMW := by
    rcases rem52b?_some hop with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_rem52b hl htemp hop hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_rem52b hA hop hxv hyv hxf hyf hcx hcy ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_rem52b has hkn hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

end Cases

/-! ## The theorem -/

/-- One value of G52's group B: it runs its one Prog, keeps the match and `G3Inv`, and empties the
upper-bit table. -/
theorem vk52b_step {env : Env} {H : Hooks} {lc : LocCtx} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (F : Facts lc sym text az ez ps.toList ret E) (hVK : VK52b lc v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' osp ∧ UOKL m'
      (uStep35 lc L v) := by
  cases hVK with
  | rem hop hsz hao hbo hro h8 hcx hcy =>
    obtain ⟨r, hvh, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g52b_rem (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo
      hro h8 hcx hcy hvs htemp hs
    refine ⟨m', h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_52b hop]
    exact fun e he => by cases he

end GoFV.Proof.Gen
