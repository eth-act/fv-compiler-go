import GoFV.Proof.Gen.G25
import GoFV.Proof.Gen.Spec26

/-!
# Soundness of the genssa validator's slice G26: functions with no arm64 op
(`docs/plans/proofs3.md` §4)

`g26_value`, `g26_term`, `g26_nilPanic`, `g26_boundsPanic`: `g25_value`'s, `g25_term`'s,
`g25_nilPanic`'s and `g25_boundsPanic`'s statements over `checkG26`. On a function with an arm64
op, `checkG26` is `checkG25` (`checkG26_lowered`) and the theorems are G25's. On one without
(`Func.lowered = false`), `runLoc` reads values with Phase 1's `Val.retype` (`lmode_retypeP`), not
as registers. At a register's shape that is `Val.retypeL`'s value or `poison`
(`retype_cases`), so a value read stays related to its machine word and of its class
(`valRel_retype`, `fits_retype`, `arg_relP`). The values `checkNL` accepts are G1's `MakeResult`,
`InlMark` and `Copy`:

* `InlMark` and `MakeResult` change nothing (`stepLoc_inlMark`, `write_result_noopP`) and have no
  code;
* `Copy` writes its argument at its shape, a register move `MOVD` or no code within one register
  (`stepLoc_copyP`, `op_regN`).

Every block is a `Ret`, which goes to no successor, so `g26_term` holds vacuously; no value
is a nil check or a bounds panic.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## Phase 1's reads -/

section Reads

variable {lc : LocCtx} {s s' : LocState} {env : Env} {v : Value}

/-- A function with no arm64 op reads values as Phase 1 does. -/
theorem lmode_retypeP {f : Func} (hl : f.lowered = false) (t : Ty) (v : Val) :
    (LMode.loc f).retype t v = v.retype t := by
  simp [LMode.loc, LMode.sched, LMode.retype, hl]

/-- At a register's shape, Phase 1's retyping is the register read's, or `poison` where the
register read widens. -/
theorem retype_cases {t : Ty} {c : Nat} (hc : cls t = some c) (v : Val) :
    v.retype t = v.retypeL t ∨ v.retype t = .poison := by
  cases t with
  | int w' =>
    cases v with
    | int w x =>
      simp only [Val.retypeL, Val.widen]
      split
      · right
        simp only [Val.retype]
        split
        · omega
        · rfl
      · left; rfl
    | bool b => right; rfl
    | _ => left; rfl
  | ptr _ =>
    cases v with
    | int w x =>
      simp only [Val.retypeL, Val.widen]
      split
      · right
        cases w <;> simp_all [Width.bits] <;> rfl
      · left; rfl
    | bool b => right; rfl
    | _ => left; rfl
  | bool => left; cases v <;> rfl
  | _ => simp [Gen.Check.cls] at hc

theorem retype_poison (t : Ty) : Val.retype t .poison = .poison := by
  cases t <;> rfl

theorem valRel_retype {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) {c : Nat} {t : Ty}
    {v : Val} {r : BitVec 64} (hc : cls t = some c) (hf : Fits c v) (hv : ValRel ι v r) :
    ValRel ι (v.retype t) r := by
  rcases retype_cases hc v with h | h
  · rw [h]; exact valRel_retypeL hA hc hf hv
  · rw [h]; trivial

theorem fits_retype {c : Nat} {t : Ty} (hc : cls t = some c) (v : Val) : Fits c (v.retype t) := by
  rcases retype_cases hc v with h | h
  · rw [h]; exact fits_retypeL hc v
  · rw [h]; trivial

/-- A value with a register home, read at its shape (Phase 1). -/
theorem read_regP {a r c : Nat} (hl : lc.ctx.f.lowered = false)
    (hh : lc.home a = some (.reg r)) (hc : cls (lc.ty a) = some c) :
    s.read lc a = .ok ((s.reg (lc.ty a) r).retype (lc.ty a)) := by
  have hraw : s.raw lc a = .ok (s.reg (lc.ty a) r) := by
    unfold LocState.raw
    cases ht : lc.ty a <;> simp_all [Gen.Check.cls]
  unfold LocState.read
  rw [hraw]; simp only [lmode_retypeP hl]
  rfl

/-- The memory argument (Phase 1). -/
theorem read_memP {a : Nat} (hl : lc.ctx.f.lowered = false) (hh : lc.home a = none)
    (ht : memTy (lc.ty a) = true) {mm : Mem} (hm : s.mem = .mem mm) :
    s.read lc a = .ok (.mem mm) := by
  have ht' : lc.ty a = .mem := by cases h : lc.ty a <;> simp_all [memTy]
  have hraw : s.raw lc a = .ok s.mem := by
    unfold LocState.raw
    rw [hh, ht']
  unfold LocState.read
  rw [hraw, hm]; simp only [lmode_retypeP hl, ht']
  rfl

theorem stepLoc_noclobberP (hl : lc.ctx.f.lowered = false) (ht : (lc.temps[v.id]?).join = none)
    (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg) (h2 : v.op ≠ .StoreReg)
    (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv r, v.args.toList.mapM (s.read lc) = .ok argv ∧
      evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = .ok r ∧
      s' = s.write lc v.id (r.retype (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_ok_eval hne h1 h2 h3 h4 h
  refine ⟨argv, r, hm, hr, ?_⟩
  rw [clobber_none hc hc0 hc1 ht hf, lmode_retypeP hl]

/-- `Copy` of one argument (Phase 1): the argument at the value's shape. -/
theorem stepLoc_copyP (hl : lc.ctx.f.lowered = false) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .Copy) {a : ID} (ha : v.args = #[a]) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a = .ok x ∧ s' = s.write lc v.id (x.retype (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobberP hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hm
  change [a].mapM (s.read lc) = _ at hm
  rw [show [a].mapM (s.read lc) = (s.read lc a).bind fun x => .ok [x] from rfl] at hm
  cases hx : s.read lc a with
  | ok x =>
    rw [hx] at hm; cases hm
    have he : evalOpL true env lc.ctx s.fr v [x] (lc.ty v.id) = .ok x := by
      unfold evalOpL evalOp frameVal; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨_, rfl, rfl⟩
  | panic e m => rw [hx] at hm; cases hm
  | stuck msg => rw [hx] at hm; cases hm

/-- `MakeResult` (Phase 1): the tuple of its arguments at the value's shape. -/
theorem stepLoc_makeResultP (hl : lc.ctx.f.lowered = false) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .MakeResult) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Val.tuple argv).retype (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobberP hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = .ok (.tuple argv) := by
    unfold evalOpL evalOp frameVal; rw [hop]; rfl
  rw [he] at hr; cases hr
  exact ⟨argv, hm, rfl⟩

theorem retypePre_zip : ∀ (ts : List Ty) (xs : List Val), ts.length = xs.length →
    Val.retypePre ts xs = some (List.zipWith (fun t x => x.retype t) ts xs)
  | [], [], _ => rfl
  | t :: ts, x :: xs, h => by
    simp only [Val.retypePre, List.zipWith_cons_cons]
    rw [retypePre_zip ts xs (by simpa using h)]
    rfl

/-- `MakeResult` writes nothing that changes the state (Phase 1, `resultsTy`). -/
theorem write_result_noopP {mm : Mem} {vid : ID} {args : Array ID} {argv : List Val}
    (hl : lc.ctx.f.lowered = false) (hmm : s.mem = .mem mm)
    (hh : lc.home vid = none ∨ lc.home vid = some (.results #[]))
    (hty : resultsTy lc args (lc.ty vid) = true)
    (hmem : ∀ a ∈ args.toList, memTy (lc.ty a) = true → lc.home a = none)
    (hargv : args.toList.mapM (s.read lc) = .ok argv) :
    s.write lc vid ((Val.tuple argv).retype (lc.ty vid)) = s := by
  obtain ⟨hlen, hk⟩ := mapM_res hargv
  cases hT : lc.ty vid with
  | tuple ts =>
    rw [hT] at hty
    simp only [resultsTy, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hty
    obtain ⟨htl, hall⟩ := hty
    have hlen' : ts.length = argv.length := by rw [htl, hlen]; simp
    have hw : (Val.tuple argv).retype (.tuple ts) =
        .tuple (List.zipWith (fun t x => x.retype t) ts argv) := by
      simp only [Val.retype, retypePre_zip ts argv hlen']
    have hw2 : s.write lc vid ((Val.tuple argv).retype (.tuple ts)) =
        s.writeParts ts (List.zipWith (fun t x => x.retype t) ts argv) [] := by
      rw [hw]
      unfold LocState.write
      rw [hT]
      rcases hh with h | h
      · simp only [h, Val.partsOf]; rfl
      · simp only [h]
        simp [Val.partsOf, Location.regList]
    rw [hw2]
    refine writeParts_noop ts _ (fun k hkt hkx => ?_)
    have hka : k < args.toList.length := by rw [← hlen]; simp at hkx; omega
    have hz := hall (ts[k], args.toList[k]) (List.mem_iff_getElem.2 ⟨k, by simp; omega, by simp⟩)
    simp only [Bool.not_eq_true', Bool.or_eq_true] at hz
    refine ⟨by simpa using hz.1, fun hmt => ?_⟩
    simp only [List.getElem_zipWith]
    have hamt : memTy (lc.ty args.toList[k]) = true := by
      rcases hz.2 with h | h
      · rw [hmt] at h; cases h
      · exact h
    have hrd := hk k hka (by omega)
    rw [read_memP hl (hmem _ (List.getElem_mem hka) hamt) hamt hmm] at hrd
    have hx : argv[k] = .mem mm := (Res.ok.inj hrd).symm
    rw [hx, memTy_eq hmt, hmm]
    rfl
  | _ => rw [hT] at hty; simp [resultsTy] at hty

end Reads

/-! ## One value -/

section Value

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}
  {P : BitVec 64 → Prop}

/-- A register argument read at its shape (Phase 1): related to its machine register and of its
class. -/
theorem arg_relP (hA : AddrAgree E.ι) (hl : lc.ctx.f.lowered = false)
    (hm : LocMatch E s b i m) (hinv : CoreInv ι P K s) {a r c k : Nat}
    (hh : lc.home a = some (.reg r)) (hc : cls (lc.ty a) = some c)
    (hK : r ≠ zeroReg → K r = some c)
    (hk : (r = zeroReg ∧ k = 31) ∨ (k < 31 ∧ objX? r = some (BitVec.ofNat 5 k))) :
    ∃ x, s.read lc a = .ok x ∧ ValRel E.ι x (m.rX (BitVec.ofNat 5 k)) ∧ Fits c x := by
  refine ⟨_, read_regP hl hh hc, ?_, fits_retype hc _⟩
  rcases hk with ⟨rfl, rfl⟩ | ⟨hk, hobj⟩
  · rw [rX_31]
    simp only [LocState.reg, beq_self_eq_true, ↓reduceIte]
    exact valRel_retype hA hc (fits_retypeL hc _) (valRel_zero hc)
  · rw [rX_lt hk]
    have hrz : r ≠ zeroReg := by
      intro h; subst h; simp [objX?, zeroReg] at hobj
    simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
    cases hv : s.regs[r]? with
    | none => simp only [Option.getD_none, retype_poison]; trivial
    | some v =>
      simp only [Option.getD_some]
      exact valRel_retype hA hc (hinv.regs r v c hrz hv (hK hrz)) ((hm.regs r v hv).1 _ hobj)

/-- A value whose one Prog writes its register (`op_reg` from the facts it uses). -/
theorem op_regN (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    (hm : LocMatch E s b i m)
    (hinv : CoreInv E.ι P K s) (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {sh : Shape} (hone : OneAt psA j sh j')
    {r c kd : Nat} {x : Val} {val : BitVec 64} (hd : destOK r = true)
    (hkd : kd < 32) (hrk : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + kd))
    (hx : ValRel E.ι x val) (hfx : Fits c x) (hKL : KLe K' (kSet K r (some c)))
    (hstep : ∀ k (hk : k < psA.toList.length), sh.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m.wX (BitVec.ofNat 5 kd) val with pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E (s.setReg r x) b (i + 1) m' ∧ CoreInv E.ι P K' (s.setReg r x) ∧
      (s.setReg r x).slots = s.slots := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt (H := H) hnd hlt hret rfl hone m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv hd hkd hrk hx hfx (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at hnd hlt hret hk rfl (hstep k hk hok)), hlm, hinv'.mono hKL, rfl⟩

/-- One value of a function with no arm64 op (`VK`'s `InlMark`, `Copy` and `MakeResult`), in
Phase 1's mode. -/
theorem nl_core (hl : lc.ctx.f.lowered = false) (hA : AddrAgree E.ι)
    (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s) {kd : VKind}
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') (hvs : VStep psA kd j j')
    (hops : v.op = .MakeResult ∨ v.op = .InlMark ∨ v.op = .Copy)
    (hVK : VK lc v kd) (htemp : (lc.temps[v.id]?).join = none)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι P K' s' ∧ s'.slots = s.slots := by
  have hnone : ∀ {r : Nat}, lc.home v.id = none → r ≠ zeroReg → lc.home v.id ≠ some (.reg r) :=
    fun h _ => by rw [h]; nofun
  cases hVK with
  | inl hop hh hi =>
    exact op_none hm hinv (stepLoc_inlMark htemp hop hh hi hs)
      (by rw [hj', hj, show j' = j from hvs]) (knext_same hK (Or.inr fun _ => hnone hh))
  | copyMem hop hmt hsz hma hh =>
    obtain ⟨a, ha0, hamt, hah⟩ := memArg_spec hma
    obtain ⟨x, hx, rfl⟩ := stepLoc_copyP hl htemp hop (arr1 hsz ha0) hs
    obtain ⟨mm, hmm, -⟩ := hm.mem
    rw [read_memP hl hah hamt hmm] at hx
    cases hx
    refine op_none hm hinv ?_ (by rw [hj', hj, show j' = j from hvs])
      (knext_same hK (Or.inr fun _ => hnone hh))
    rw [write_mem hh hmt, memTy_eq hmt, show (Val.mem mm).retype .mem = .mem mm from rfl, ← hmm]
  | copySame hop hmt hsz hao hro =>
    obtain ⟨a, r1, ha0, hah, hor1, hca⟩ := argObj_spec hao
    obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
    obtain rfl := objOf?_inj hor1 hor2
    obtain ⟨k, hk32, ho, hkk⟩ := objOf?_some hor1
    rw [ho] at hor1
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨x, hx, hxv, hxf⟩ := arg_relP hA hl hm hinv hah hca (kread_arg hR hnp ha0 hah hca) hkk
    obtain ⟨x', hx', rfl⟩ := stepLoc_copyP hl htemp hop (arr1 hsz ha0) hs
    rw [hx] at hx'
    cases hx'
    rw [write_reg hvh hcv]
    obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv hd hk32 hor1
      (valRel_retype hA hcv hxf hxv) (fits_retype hcv _) (b' := b) (i' := i + 1)
    rw [wX_rX_self, hj', show j' = j from hvs, ← hj, ← hm.pc] at hlm
    exact ⟨m, .refl, hlm, hinv'.mono (knext_set hK hnp hvh hcv), rfl⟩
  | copyMov hop hmt hsz hao hro hne =>
    obtain ⟨a, r1, ha0, hah, hor1, hca⟩ := argObj_spec hao
    obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
    obtain ⟨ka, hka, rfl, hkka⟩ := objOf?_some hor1
    obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor2
    subst hrd
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨x, hx, hxv, hxf⟩ := arg_relP hA hl hm hinv hah hca (kread_arg hR hnp ha0 hah hca) hkka
    obtain ⟨x', hx', rfl⟩ := stepLoc_copyP hl htemp hop (arr1 hsz ha0) hs
    rw [hx] at hx'
    cases hx'
    rw [write_reg hvh hcv]
    exact op_regN hnd hlt hret hm hinv hj hj' hvs hd hkd hor2 (valRel_retype hA hcv hxf hxv)
      (fits_retype hcv _) (knext_set hK hnp hvh hcv) (fun k hk hok => by
        obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
        rw [progStep_movReg hka hkd (nextAddr_pcAt hnd hk) has hf ht, wX_pc] <;> rfl)
  | result hop hh hty hmem _ =>
    obtain ⟨argv, hargv, rfl⟩ := stepLoc_makeResultP hl htemp hop hs
    obtain ⟨mm, hmm, -⟩ := hm.mem
    exact op_none hm hinv (write_result_noopP hl hmm hh hty hmem hargv)
      (by rw [hj', hj, show j' = j from hvs])
      (knext_same hK (Or.inr fun r _ => by rcases hh with h | h <;> rw [h] <;> nofun))
  | phi hop => rcases hops with h | h | h <;> rw [h] at hop <;> cases hop
  | zero hop => rcases hops with h | h | h <;> rw [h] at hop <;> cases hop
  | movConst hop => rcases hops with h | h | h <;> rw [h] at hop <;> cases hop
  | alu hop => rcases hops with h | h | h <;> rcases hop with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] at h' <;>
      cases h'
  | aluK hop => rcases hops with h | h | h <;> rcases hop with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] at h' <;>
      cases h'
  | cmp hop => rcases hops with h | h | h <;> rw [h] at hop <;> cases hop
  | cmpK hop => rcases hops with h | h | h <;> rw [h] at hop <;> cases hop
  | load hop => rcases hops with h | h | h <;> rw [h] at hop <;> cases hop
  | store hop => rcases hops with h | h | h <;> rw [h] at hop <;> cases hop

/-- The homes of `checkNL`'s values: none, a register, or `MakeResult`'s empty `results`. -/
theorem nl_homes (hnp : v.op ≠ .Phi) {kd : VKind} (hVK : VK lc v kd) :
    (∀ rs, lc.home v.id = some (.results rs) → rs = #[]) ∧
      ∀ a b, lc.home v.id ≠ some (.pair a b) := by
  have hreg : ∀ r, lc.home v.id = some (.reg r) →
      (∀ rs, lc.home v.id = some (.results rs) → rs = #[]) ∧
        ∀ a b, lc.home v.id ≠ some (.pair a b) :=
    fun r h => ⟨fun rs h' => by (rw [h] at h'; cases h'), fun a b h' => by (rw [h] at h'; cases h')⟩
  have hnone : lc.home v.id = none →
      (∀ rs, lc.home v.id = some (.results rs) → rs = #[]) ∧
        ∀ a b, lc.home v.id ≠ some (.pair a b) :=
    fun h => ⟨fun rs h' => by (rw [h] at h'; cases h'), fun a b h' => by (rw [h] at h'; cases h')⟩
  cases hVK with
  | inl _ hh => exact hnone hh
  | copyMem _ _ _ _ hh => exact hnone hh
  | copySame _ _ _ _ hro => obtain ⟨r, hh, -⟩ := resObj_spec hro; exact hreg r hh
  | copyMov _ _ _ _ hro => obtain ⟨r, hh, -⟩ := resObj_spec hro; exact hreg r hh
  | result _ hh =>
    rcases hh with hh | hh
    · exact hnone hh
    · exact ⟨fun rs h' => by (rw [hh] at h'; cases h'; rfl),
        fun a b h' => by (rw [hh] at h'; cases h')⟩
  | phi hop => exact absurd hop hnp
  | zero _ _ hh => exact hreg _ hh
  | movConst _ _ hro => obtain ⟨r, hh, -⟩ := resObj_spec hro; exact hreg r hh
  | alu _ _ _ _ hro => obtain ⟨r, hh, -⟩ := resObj_spec hro; exact hreg r hh
  | aluK _ _ _ hro => obtain ⟨r, hh, -⟩ := resObj_spec hro; exact hreg r hh
  | cmp _ _ _ hh => exact hnone hh
  | cmpK _ _ _ hh => exact hnone hh
  | load _ _ _ _ _ hro => obtain ⟨r, hh, -⟩ := resObj_spec hro; exact hreg r hh
  | store _ _ _ _ hh => exact hnone hh

theorem narrowLd?_nl (hops : v.op = .MakeResult ∨ v.op = .InlMark ∨ v.op = .Copy) :
    narrowLd? lc v = none := by
  rcases hops with hop | hop | hop <;> · unfold narrowLd?; rw [hop]; rfl

end Value

/-! ## The theorems -/

/-- A value `checkNL` accepted that is not an activation value is a `MakeResult`, `InlMark` or
`Copy`. -/
theorem nl_ops {lc : LocCtx} {g : G2In} {ps : Array Prog} {bstart : ID → Option Nat}
    {tab : PcTab} {kt : KTab} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value}
    (hc : checkNL lc ps bstart g = .ok (tab, kt))
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) : v.op = .MakeResult ∨ v.op = .InlMark ∨ v.op = .Copy := by
  obtain ⟨c, hlc, -, -, -, hvk, -, -, -, -, -, -, -, hblocks, -, -⟩ := checkNL_spec hc
  subst hlc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, -⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, -⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  exact (vkindNL_spec hkd hen).2.1

/-- **G26, values.** `g25_value`'s statement over `checkG26`. -/
theorem g26_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG26 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOK m (uAt lc blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOK m' (uAt lc blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | true =>
    exact g25_value (checkG26_lowered hl hc) hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hs
  | false =>
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkNL_spec (checkG26_nl hl hc)
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
  obtain ⟨htemp, hops, kd1, rfl, hVK⟩ := vkindNL_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  obtain ⟨m', h1, h2, h3, h4⟩ := nl_core (H := H) hl hA hnd hlt hret hm hinv.core hj hj'
    (vstep_v2 hvs) hops hVK htemp (kread_of_reads hreads)
    (knext_kStep fun hnp => nl_homes hnp hVK) hs
  have hu1 : uAt c.cx.lc blk (i + 1) = uEntry c.cx.lc v := by simp [uAt, hi, hv]
  have hue : uEntry c.cx.lc v = none := by simp only [uEntry, narrowLd?_nl hops]
  rw [kAt_succ hi hv, hu1, hue]
  exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, fun k v hk => hinv.slots k v (h4 ▸ hk)⟩,
    trivial⟩

/-- **G26, nil panics.** `g25_nilPanic`'s statement over `checkG26`. -/
theorem g26_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG26 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | true => exact g25_nilPanic (checkG26_lowered hl hc) hE hbid hb hi hv hop hm hinv hs
  | false =>
    rcases nl_ops (checkG26_nl hl hc) hbid hb hi hv (by rw [hop]; rfl) with h | h | h <;>
      rw [h] at hop <;> cases hop

/-- **G26, bounds panics.** `g25_boundsPanic`'s statement over `checkG26`, under `BoundsOK`. -/
theorem g26_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG26 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | true => exact g25_boundsPanic (checkG26_lowered hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | false =>
    have hen : entryOp24 v.op = false := by
      rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
    rcases nl_ops (checkG26_nl hl hc) hbid hb hi hv hen with h | h | h <;> rw [h] at hop <;>
      cases hop

/-- **G26, terminators.** `g25_term`'s statement over `checkG26`; a function with no arm64 op
has only `Ret` blocks, which go to no successor. -/
theorem g26_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG26 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  cases hl : lc.ctx.f.lowered with
  | true => exact g25_term (checkG26_lowered hl hc) hE hbid hb hm hinv hpre ht
  | false =>
    obtain ⟨-, -, -, -, -, -, -, hr, -⟩ := checkNL_spec (checkG26_nl hl hc)
    obtain ⟨R, -, hn⟩ := stepTermLoc_gen ht
    exact (stepTermL_ret (allRet_spec hr hbid hb) hn).elim

end GoFV.Proof.Gen
