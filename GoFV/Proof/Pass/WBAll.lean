import GoFV.Proof.Pass.WBBlock

/-!
# writebarrier: every value of a chain (issue #36)

`Setup`: the static facts about block `b` of `f` and its chain in `g` (`chainRuns?`, `blockOK`).
`Cov`: the source facts a value of the chain needs, by role (a kept non-`Phi` value, a run's
store and a nil check copied: the source evaluated them in the reference frame `Gr`; the `WB`:
the run's memory is a memory). `local_seg`/`local_t`: a non-`Phi` value listed in a segment or
a buffer block of the chain whose `Cov` holds evaluates as `QR` says (`LocalQ`), dispatching on
`roleOf` to the local steps of `WBLocal`.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

/-- The static facts about block `b` of `f` (table entry `B`) and its chain (runs `rs`, last
block `l`) in `g`. -/
structure Setup (c : WBCheck.Ctx) (b : ID) (B : Block) (rs : List Run) (l : ID) : Prop where
  ctx : ctxOf c.tabs c.f c.g = some c
  wf : ∃ ce, WF ce c.f
  wg : ∃ ce, WF ce c.g
  entry : c.g.entry = c.f.entry
  own : c.g.ownAux = c.f.ownAux
  memTy : memTyOK c.tabs c.f = true
  hb : b ∈ c.f.blocks
  hB : c.f.block? b = some B
  ch : chainRuns? c.f c.g b = some (rs, l)
  ok : c.blockOK b = true

/-- `x` is listed in segment `j` of the chain. -/
def InSeg (c : WBCheck.Ctx) (b : ID) (rs : List Run) (j : Nat) (x : ID) : Prop :=
  ∃ s, (segsOf b rs)[j]? = some s ∧ x ∈ vals c.g s

/-- `x` is listed in the buffer block of run `j`. -/
def InT (c : WBCheck.Ctx) (rs : List Run) (j : Nat) (x : ID) : Prop :=
  ∃ r, rs[j]? = some r ∧ x ∈ vals c.g r.sp.t

/-- The source evaluated `x` in `Gr`. -/
def Ev (env : Env) (c : WBCheck.Ctx) (Gr : Frame) (x : ID) : Prop :=
  ∃ u y, c.f.value? x = some u ∧ Gr.regs[x]? = some (some y) ∧
    evalValue env (Ctx.make c.tabs c.f) Gr u = .ok y

/-- The source facts a value of the chain needs, by role. -/
def Cov (env : Env) (c : WBCheck.Ctx) (rs : List Run) (Gr : Frame) (x : ID) : Prop :=
  match c.roleOf rs x with
  | .held => c.K.getD x false = true → ∀ u, c.f.value? x = some u → u.op ≠ .Phi → Ev env c Gr x
  | .tgt j k => ∃ r s, rs[j]? = some r ∧ r.src[k]? = some s ∧ Ev env c Gr s
  | .ncEnd j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Ev env c Gr n
  | .ncThen j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Ev env c Gr n
  | .wb j => ∃ M, RunMem Gr rs j M
  | _ => True

/-! ## Roles: the inverse direction -/

private theorem vals_of {h : Func} {s : ID} {T : Block} (hT : h.block? s = some T) :
    vals h s = T.values := by
  unfold vals; rw [hT]; rfl

/-- The roles `roleRun` never gives. -/
private def notRun : Role → Bool
  | .held | .wbaddr | .const0 | .lazy | .invalid => true
  | _ => false

private theorem thenRole_notRun (v : Value) (j : Nat) : notRun (thenRole v j) = false := by
  unfold thenRole
  repeat' split
  all_goals rfl

private theorem roleRun_notRun {g : Func} {x : ID} :
    ∀ {rs : List Run} {k : Nat}, notRun (roleRun g x rs k) = false
  | [], _ => rfl
  | r :: rs, k => by
    rw [roleRun]
    by_cases h1 : (x == r.sp.load) = true
    · rw [if_pos h1]; rfl
    rw [if_neg h1]
    by_cases h2 : (x == r.sp.flag) = true
    · rw [if_pos h2]; rfl
    rw [if_neg h2]
    by_cases h3 : (x == r.phi) = true
    · rw [if_pos h3]; rfl
    rw [if_neg h3]
    by_cases h4 : (r.ncEnd == some x) = true
    · rw [if_pos h4]; rfl
    rw [if_neg h4]
    cases hk : r.tgt.idxOf? x with
    | some k' => rfl
    | none =>
      dsimp only
      by_cases h5 : (vals g r.sp.t).contains x = true
      · rw [if_pos h5]
        cases hv : g.value? x with
        | none => rfl
        | some v => exact thenRole_notRun v k
      · rw [if_neg h5]; exact roleRun_notRun

private theorem roleOf_cases (c : WBCheck.Ctx) (rs : List Run) (x : ID) :
    (c.isWbaddr x = true ∧ c.roleOf rs x = .wbaddr) ∨
    (c.isConst0 x = true ∧ c.roleOf rs x = .const0) ∨
    (c.held x = true ∧ c.roleOf rs x = .held) ∨
    notRun (c.roleOf rs x) = false ∨ c.roleOf rs x = otherRole c.g x := by
  unfold Ctx.roleOf
  by_cases h1 : c.isWbaddr x = true
  · rw [if_pos h1]; exact .inl ⟨h1, rfl⟩
  rw [if_neg h1]
  by_cases h2 : c.isConst0 x = true
  · rw [if_pos h2]; exact .inr (.inl ⟨h2, rfl⟩)
  rw [if_neg h2]
  by_cases h3 : c.held x = true
  · rw [if_pos h3]; exact .inr (.inr (.inl ⟨h3, rfl⟩))
  rw [if_neg h3]
  right; right; right
  generalize hR : roleRun c.g x rs 0 = R
  have hn : notRun R = false := hR ▸ roleRun_notRun
  cases R
  all_goals first | exact .inr rfl | exact .inl hn

private theorem otherRole_spec {g : Func} {x : ID} {ρ : Role} (h : otherRole g x = ρ) :
    ρ = .invalid ∨ ρ = .none ∨ (ρ = .lazy ∧ ∃ v, g.value? x = some v ∧
      (v.op = .SB ∨ v.op = .SP ∨ v.op = .Const32 ∨ v.op = .Addr)) := by
  unfold otherRole at h
  split at h
  · rename_i v hv
    split at h
    · exact .inl h.symm
    · split at h
      · rename_i hc
        refine .inr (.inr ⟨h.symm, v, hv, ?_⟩)
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
        rcases hc with ⟨((h1 | h1) | h1), -⟩ | ⟨h1, -⟩
        · exact .inl h1
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inl h1))
        · exact .inr (.inr (.inr h1))
      · exact .inr (.inl h.symm)
  · exact .inr (.inl h.symm)

private theorem roleOf_wbaddr_inv {c : WBCheck.Ctx} {rs : List Run} {x : ID}
    (h : c.roleOf rs x = .wbaddr) : c.isWbaddr x = true := by
  rcases roleOf_cases c rs x with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | h2 | h2
  · exact h1
  all_goals rw [h] at h2
  · cases h2
  · cases h2
  · simp [notRun] at h2
  · rcases otherRole_spec h2.symm with h3 | h3 | ⟨h3, -⟩ <;> cases h3

private theorem roleOf_const0_inv {c : WBCheck.Ctx} {rs : List Run} {x : ID}
    (h : c.roleOf rs x = .const0) : c.isConst0 x = true := by
  rcases roleOf_cases c rs x with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩ | h2 | h2
  · rw [h] at h2; cases h2
  · exact h1
  all_goals rw [h] at h2
  · cases h2
  · simp [notRun] at h2
  · rcases otherRole_spec h2.symm with h3 | h3 | ⟨h3, -⟩ <;> cases h3

/-- A `lazy` value's op is speculation-safe. -/
private theorem lazy_safe {c : WBCheck.Ctx} {rs : List Run} {x : ID} {w : Value}
    (h : c.roleOf rs x = .lazy) (hw : c.g.value? x = some w) : specSafeOp w.op = true := by
  rcases roleOf_cases c rs x with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | h2 | h2
  all_goals rw [h] at h2
  · cases h2
  · cases h2
  · cases h2
  · simp [notRun] at h2
  · rcases otherRole_spec h2.symm with h3 | h3 | ⟨-, v, hv, hop⟩
    · cases h3
    · cases h3
    · rw [hw] at hv; cases hv
      rcases hop with hop | hop | hop | hop <;> rw [hop] <;> decide

private theorem roleOK_none {c : WBCheck.Ctx} {b : ID} {B : Block} {segs : List ID}
    {rs : List Run} {inT : Bool} {j : Nat} {x : ID} (h : c.roleOK b B segs rs inT j x = true)
    (hρ : c.roleOf rs x = .none) : False := by
  unfold Ctx.roleOK at h
  split at h
  · cases h
  · rw [hρ] at h; cases h

/-- A buffer-block role's op. -/
private theorem then_op {c : WBCheck.Ctx} {rs : List Run} {x : ID} {ρ : Role} {j : Nat} {o : Op}
    (hρ : c.roleOf rs x = ρ) (ht : thenOp ρ = some (j, o)) {w : Value}
    (hw : c.g.value? x = some w) : w.op = o := by
  have ht' : thenOp (c.roleOf rs x) = some (j, o) := by rw [hρ]; exact ht
  obtain ⟨-, -, -, w', hw', hop⟩ := roleOf_then ht'
  rw [hw] at hw'; cases hw'; exact hop

private theorem lazy_of_wbaddr {c : WBCheck.Ctx} {x : ID} (h : c.isWbaddr x = true) :
    ∃ c0, c.lazy = some (x, c0) := by
  unfold Ctx.isWbaddr at h
  cases hz : c.lazy with
  | none => rw [hz] at h; cases h
  | some p =>
    rw [hz] at h
    obtain ⟨wa, c0⟩ := p
    simp only [Option.any_some, beq_iff_eq] at h
    subst h
    exact ⟨c0, rfl⟩

private theorem lazy_of_const0 {c : WBCheck.Ctx} {x : ID} (h : c.isConst0 x = true) :
    ∃ wa, c.lazy = some (wa, x) := by
  unfold Ctx.isConst0 at h
  cases hz : c.lazy with
  | none => rw [hz] at h; cases h
  | some p =>
    rw [hz] at h
    obtain ⟨wa, c0⟩ := p
    simp only [Option.any_some, beq_iff_eq] at h
    subst h
    exact ⟨wa, rfl⟩

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-! ## Static facts -/

private theorem run (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    c.runOK b B (segsOf b rs) rs j r = true :=
  (blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j r hr

private theorem runOf (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    runOf? c.f c.g r.sp = some r :=
  ((chainRuns_spec S.ch).1 j r hr).2.2.2

/-- A value listed in a block of the chain has its ID. -/
private theorem vid (S : Setup c b B rs l) {s x : ID} {w : Value}
    (hs : s ∈ segsOf b rs ++ rs.map (·.sp.t)) (hx : x ∈ vals c.g s)
    (hw : c.g.value? x = some w) : w.id = x := by
  obtain ⟨ce, hwg⟩ := S.wg
  have hbl := (blockOK_spec S.ok S.hB S.ch).2.2.2.1 s hs
  cases hC : c.g.block? s with
  | none => rw [vals, hC] at hx; simp at hx
  | some C =>
    rw [vals_of hC] at hx
    obtain ⟨v, hv, hid, -⟩ := hwg.valueId s C ⟨hbl, hC⟩ x hx
    rw [hw] at hv; cases hv; exact hid

/-- A value of `B` has its ID. -/
private theorem fid (S : Setup c b B rs l) {x : ID} {u : Value} (hx : x ∈ B.values)
    (hu : c.f.value? x = some u) : u.id = x := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨v, hv, hid, -⟩ := hwf.valueId b B ⟨S.hb, S.hB⟩ x hx
  rw [hu] at hv; cases hv; exact hid

private theorem t_ok (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) {x : ID}
    (hx : x ∈ vals c.g r.sp.t) : c.roleOK b B (segsOf b rs) rs true j x = true := by
  obtain ⟨-, -, ⟨T, hT, -, -, -, -, -, hall⟩, -⟩ := runOK_spec (S.run hr)
  rw [vals_of hT] at hx
  exact hall x hx

/-- The run's `WB` has at most 8 slots. -/
private theorem wbN8 (S : Setup c b B rs l) {a : ID} {i : Nat} (ha : c.roleOf rs a = .wb i) :
    ∀ r, rs[i]? = some r → r.wbN ≤ 8 := by
  intro r hr
  have ht : thenOp (c.roleOf rs a) = some (i, .WB) := by rw [ha]; rfl
  obtain ⟨r', hr', hat, wa, hwa, -⟩ := roleOf_then ht
  obtain ⟨-, -, r3, hr3, -, -, -, h8, -⟩ := roleOK_wb (S.t_ok hr' hat) hwa ha
  rw [hr] at hr3; cases hr3; exact h8

/-- The source nil check's memory is the run's memory. -/
private theorem nc_mem (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) {n : ID}
    (hn : r.nc = some n) {u : Value} (hu : c.f.value? n = some u) {p mS : ID}
    (hu2 : u.args = #[p, mS]) (hsrc : ∀ x ∈ r.src, x ∈ B.values ∧ c.K.getD x false = false) :
    mS = r.sp.mem := by
  obtain ⟨-, -, -, -, hnc, -⟩ := runOf_spec (S.runOf hr)
  obtain ⟨x0, v0, a, nv, hx0, hv0, -, ha, hnv, -, hm, hid⟩ := hnc n hn
  obtain ⟨ce, hwf⟩ := S.wf
  have hx0B := (hsrc x0 (List.mem_of_getElem? hx0)).1
  obtain ⟨bid, B', hbB', haB'⟩ :=
    hwf.argListed b B x0 v0 ⟨⟨S.hb, S.hB⟩, hx0B, hv0⟩ a (Array.mem_of_getElem? ha)
  obtain ⟨v', hv', hvid, -⟩ := hwf.valueId bid B' hbB' a haB'
  rw [hnv] at hv'; cases hv'
  have han : a = n := hvid.symm.trans hid
  subst han
  rw [hu] at hnv; cases hnv
  rw [hu2] at hm
  simpa using hm

/-! ## The roles -/

private theorem loc_wbaddr (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame} {x : ID}
    {w : Value} (hw : c.g.value? x = some w) (hid : w.id = x) (hρ : c.roleOf rs x = .wbaddr) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨c0, hz⟩ := lazy_of_wbaddr (roleOf_wbaddr_inv hρ)
  have hl := (ctxOf_spec S.ctx).2.2.2.2.2
  rw [hz] at hl
  obtain ⟨⟨w', hw', hop, hsym, hty, -⟩, -⟩ := lazyOK_some hl
  rw [hw] at hw'; cases hw'
  exact local_wbaddr hw hid hρ hop hsym hty

private theorem loc_const0 (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame} {x : ID}
    {w : Value} (hw : c.g.value? x = some w) (hid : w.id = x) (hρ : c.roleOf rs x = .const0) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨wa, hz⟩ := lazy_of_const0 (roleOf_const0_inv hρ)
  have hl := (ctxOf_spec S.ctx).2.2.2.2.2
  rw [hz] at hl
  obtain ⟨-, ⟨w', hw', hop, hai, hargs, hty⟩, -⟩ := lazyOK_some hl
  rw [hw] at hw'; cases hw'
  exact local_const0 hw hid hρ hop hai hargs hty

private theorem seg_held (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hGr : Gr = { fr0 with regs := Gr.regs }) (hH : HeldGr c rs Gr) {j : Nat} {x : ID}
    {w : Value} (hok : c.roleOK b B (segsOf b rs) rs false j x = true)
    (hw : c.g.value? x = some w) (hid : w.id = x) (hnp : w.op ≠ .Phi)
    (hρ : c.roleOf rs x = .held)
    (hcov : c.K.getD x false = true → ∀ u, c.f.value? x = some u → u.op ≠ .Phi →
      Ev env c Gr x) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨-, hxB, ⟨hK, u, hu, -, hnphi⟩ | ⟨-, j', r, rfl, hr, hlast, hop, hargs, -, hty, -, hrole⟩⟩ :=
    roleOK_held hok hw hρ
  · have hK' : (keptMarks c.f c.g).getD x false = true := by
      rw [← (ctxOf_spec S.ctx).2.2.2.1]; exact hK
    obtain ⟨u', w', hu', hw', hsame, -⟩ := keptMarks_spec hK'
    rw [hu] at hu'; cases hu'
    rw [hw] at hw'; cases hw'
    have hop : u.op = w.op := by
      simp only [sameV, Bool.and_eq_true, beq_iff_eq] at hsame
      exact hsame.1.1.1.1.2
    have hnpu : u.op ≠ .Phi := hop ▸ hnp
    obtain ⟨u', y, hu', hy, hev⟩ := hcov hK u hu hnpu
    rw [hu] at hu'; cases hu'
    exact local_kept hw hu (S.fid hxB hu) hsame hρ ⟨y, hy, hev⟩
      (fun a ha z y' hq hy' => hH a z y' (availIn_spec (hnphi hnpu a ha)).1 hq hy') hGr
      S.own.symm
  · refine local_last hw hid hρ hop hargs hty fun z hq => ?_
    simp only [QR, hrole] at hq
    obtain ⟨r', s, M, m, hr', hs, hM, rfl, hW⟩ := hq
    rw [hr] at hr'; cases hr'
    obtain ⟨-, hlen, hgl, -⟩ := runOf_spec (S.runOf hr)
    have hx : r.src[r.tgt.length - 1]? = some x := by
      rw [← hlen, ← List.getLast?_eq_getElem?, hgl, hlast]
    rw [hx] at hs; cases hs
    exact ⟨M, m, hM, rfl, hW⟩

private theorem seg_nc (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame} (hH : HeldGr c rs Gr)
    {j i : Nat} {x : ID} {w : Value} (hok : c.roleOK b B (segsOf b rs) rs false j x = true)
    (hw : c.g.value? x = some w) (hid : w.id = x) (hρ : c.roleOf rs x = .ncEnd i)
    (hcov : ∃ r n, rs[i]? = some r ∧ r.nc = some n ∧ Ev env c Gr n) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨-, -, r, n, hr, hn, ⟨u, w', p, mS, hu, hw', hopu, hopw, hty, hu2, hw2, hav⟩, hphi⟩ :=
    roleOK_ncEnd hok hw hρ
  rw [hw] at hw'; cases hw'
  obtain ⟨r', n', hr', hn', u', y, hu', hy, hev⟩ := hcov
  rw [hr] at hr'; cases hr'
  rw [hn] at hn'; cases hn'
  rw [hu] at hu'; cases hu'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnc⟩ := runOK_spec (S.run hr)
  exact local_nc hH hw hid hu (S.fid (hnc n hn).1 hu)
    (fun y' hy' => by simp only [QR, hρ]; exact ⟨r, n, hr, hn, hy'⟩) ⟨y, hy, hev⟩ hopu hopw hty
    hu2 hw2 (availIn_spec hav).1
    (fun z hq _ _ => by
      simp only [QR, hphi] at hq
      obtain ⟨-, m, -, rfl, -⟩ := hq
      exact ⟨m, rfl⟩)

private theorem t_nc (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame} (hH : HeldGr c rs Gr)
    {j i : Nat} {x : ID} {w : Value} (hok : c.roleOK b B (segsOf b rs) rs true j x = true)
    (hw : c.g.value? x = some w) (hid : w.id = x) (hρ : c.roleOf rs x = .ncThen i)
    (hcov : ∃ r n, rs[i]? = some r ∧ r.nc = some n ∧ Ev env c Gr n) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨-, -, r, n, hr, hn, ⟨u, w', p, mS, hu, hw', hopu, hopw, hty, hu2, hw2, hav⟩⟩ :=
    roleOK_ncThen hok hw hρ
  rw [hw] at hw'; cases hw'
  obtain ⟨r', n', hr', hn', u', y, hu', hy, hev⟩ := hcov
  rw [hr] at hr'; cases hr'
  rw [hn] at hn'; cases hn'
  rw [hu] at hu'; cases hu'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hmh, -, hsrc, hnc⟩ := runOK_spec (S.run hr)
  have hmS : mS = r.sp.mem := S.nc_mem hr hn hu hu2 hsrc
  subst hmS
  exact local_nc hH hw hid hu (S.fid (hnc n hn).1 hu)
    (fun y' hy' => by simp only [QR, hρ]; exact ⟨r, n, hr, hn, hy'⟩) ⟨y, hy, hev⟩ hopu hopw hty
    hu2 hw2 (availIn_spec hav).1 (fun z hq M hM => ⟨M, hH _ _ _ hmh hq hM⟩)

private theorem seg_tgt (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame} (hH : HeldGr c rs Gr)
    {j i k : Nat} {x : ID} {w : Value} (hok : c.roleOK b B (segsOf b rs) rs false j x = true)
    (hw : c.g.value? x = some w) (hid : w.id = x) (hρ : c.roleOf rs x = .tgt i k)
    (hcov : ∃ r s, rs[i]? = some r ∧ r.src[k]? = some s ∧ Ev env c Gr s) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨-, -, r, s, hr, hs, -, ⟨u, w', hu, hw', hop, hty, haux, -, hsz, hback, hmt, hall⟩,
    hrole⟩ := roleOK_tgt hok hw hρ
  rw [hw] at hw'; cases hw'
  obtain ⟨r', s', hr', hs', u', y, hu', hy, hev⟩ := hcov
  rw [hr] at hr'; cases hr'
  rw [hs] at hs'; cases hs'
  rw [hu] at hu'; cases hu'
  obtain ⟨-, -, -, ⟨E, -, -, -, hnone⟩, -, -, -, -, -, -, -, -, -, -, hncρ, hsrc, -⟩ :=
    runOK_spec (S.run hr)
  obtain ⟨-, -, -, hops, -⟩ := runOf_spec (S.runOf hr)
  obtain ⟨u', hu', hopu, hlastu⟩ := hops k s hs
  rw [hu] at hu'; cases hu'
  have hlastw := (Array.getLast?_toList w.args).trans hback
  refine local_tgt (f := c.f) hw hid hρ hr hs hu (S.fid (hsrc s (List.mem_of_getElem? hs)).1 hu)
    ⟨y, hy, hev⟩ hopu hop haux hty hmt hsz hlastu hlastw ?_ ?_
  · intro z hq
    rcases k with _ | k'
    · dsimp only at hrole hq ⊢
      simp only [QR, hrole] at hq
      obtain ⟨M, m, ⟨r', hr', hM⟩, rfl, hW⟩ := hq
      rw [hr] at hr'; cases hr'
      exact ⟨M, m, hM, rfl, hW⟩
    · dsimp only at hrole hq ⊢
      simp only [QR, hrole] at hq
      obtain ⟨r', s', M, m, hr', hs', hM, rfl, hW⟩ := hq
      rw [hr] at hr'; cases hr'
      have he : r.src[k']! = s' := by simp [getElem!_def, hs']
      exact ⟨M, m, by rw [he]; exact hM, rfl, hW⟩
  · intro i' a a' hi ha ha' z y' hq hy'
    obtain ⟨h1, h2⟩ := hall i' (by omega)
    have hga : u.args[i']! = a := by simp [getElem!_def, ha]
    have hga' : w.args[i']! = a' := by simp [getElem!_def, ha']
    rw [hga, hga'] at h1 h2
    by_cases hc : r.nc = some a ∧ i' = 0
    · have h1 := h1 hc
      cases hne : r.ncEnd with
      | none =>
        have h0 := hnone hne
        rw [h0] at hc
        exact absurd hc.1 (by simp)
      | some y0 =>
        rw [hne] at h1
        simp only [Option.getD_some] at h1
        subst h1
        simp only [QR, hncρ _ hne] at hq
        obtain ⟨r', n, hr', hn, hz⟩ := hq
        rw [hr] at hr'; cases hr'
        rw [hc.1] at hn; cases hn
        rw [hz] at hy'; cases hy'; rfl
    · obtain ⟨h3, hav⟩ := h2 hc
      rw [h3] at hq
      exact hH a z y' (availIn_spec hav).1 hq hy'

/-- The run's memory is held. -/
private theorem mem_held (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    c.held r.sp.mem = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := runOK_spec (S.run hr)
  exact h

/-! ## The dispatch -/

/-- **A value of a segment.** -/
theorem local_seg (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hGr : Gr = { fr0 with regs := Gr.regs }) (hH : HeldGr c rs Gr) (hM : MemsGr Gr)
    {j : Nat} {x : ID} {w : Value} (hx : InSeg c b rs j x) (hw : c.g.value? x = some w)
    (hnp : w.op ≠ .Phi) (hcov : Cov env c rs Gr x) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨s, hs, hxs⟩ := hx
  have hok := (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.1 j s hs x hxs
  have hid := S.vid (List.mem_append_left _ (List.mem_of_getElem? hs)) hxs hw
  unfold Cov at hcov
  generalize hρ : c.roleOf rs x = ρ at hcov
  cases ρ with
  | held => exact S.seg_held hGr hH hok hw hid hnp hρ hcov
  | wbaddr => exact S.loc_wbaddr hw hid hρ
  | const0 => exact S.loc_const0 hw hid hρ
  | lazy => exact local_true hw (lazy_safe hρ hw) (fun y => by simp only [QR, hρ])
  | invalid =>
    exact local_true hw (by rw [(roleOK_invalid hok hw hρ).2.1]; decide)
      (fun y => by simp only [QR, hρ])
  | load i =>
    obtain ⟨-, rfl, r, hr, hop, hargs, hty, hwa, hm⟩ := roleOK_load hok hw hρ
    exact local_load hH hM hw hid hρ hr hop hargs hty (roleOf_wbaddr hwa) (availIn_spec hm).1
  | flag i =>
    obtain ⟨-, rfl, r, hr, hop, hargs, hty, hc, hl⟩ := roleOK_flag hok hw hρ
    exact local_flag hw hid hρ hop hargs hty hl (roleOf_const0 hc (isWbaddr_of_const0 S.ctx hc))
  | phi i =>
    obtain ⟨-, -, r, -, hop, -⟩ := roleOK_phi hok hw hρ
    exact absurd hop hnp
  | ncEnd i => exact S.seg_nc hH hok hw hid hρ hcov
  | tgt i k => exact S.seg_tgt hH hok hw hid hρ hcov
  | ncThen i => exact absurd (roleOK_ncThen hok hw hρ).1 Bool.false_ne_true
  | wb i => exact absurd (roleOK_wb hok hw hρ).1 Bool.false_ne_true
  | sel0 i => exact absurd (roleOK_sel hok hw (.inl hρ)).1 Bool.false_ne_true
  | sel1 i => exact absurd (roleOK_sel hok hw (.inr hρ)).1 Bool.false_ne_true
  | off i => exact absurd (roleOK_off hok hw hρ).1 Bool.false_ne_true
  | bstore i => exact absurd (roleOK_bstore hok hw hρ).1 Bool.false_ne_true
  | tload i => exact absurd (roleOK_tload hok hw hρ).1 Bool.false_ne_true
  | none => exact (roleOK_none hok hρ).elim

/-- **A value of a buffer block.** -/
theorem local_t (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hH : HeldGr c rs Gr) (hM : MemsGr Gr)
    {j : Nat} {x : ID} {w : Value} (hx : InT c rs j x) (hw : c.g.value? x = some w)
    (hcov : Cov env c rs Gr x) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨r, hr, hxt⟩ := hx
  have hok := S.t_ok hr hxt
  have hid := S.vid (List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_of_getElem? hr, rfl⟩))
    hxt hw
  unfold Cov at hcov
  generalize hρ : c.roleOf rs x = ρ at hcov
  cases ρ with
  | held => exact absurd (roleOK_held hok hw hρ).1 (fun h => nomatch h)
  | wbaddr => exact absurd (roleOK_lazy hok hw (.inl hρ)).1 (fun h => nomatch h)
  | const0 => exact absurd (roleOK_lazy hok hw (.inr (.inl hρ))).1 (fun h => nomatch h)
  | lazy => exact absurd (roleOK_lazy hok hw (.inr (.inr hρ))).1 (fun h => nomatch h)
  | invalid => exact absurd (roleOK_invalid hok hw hρ).1 (fun h => nomatch h)
  | load i => exact absurd (roleOK_load hok hw hρ).1 (fun h => nomatch h)
  | flag i => exact absurd (roleOK_flag hok hw hρ).1 (fun h => nomatch h)
  | phi i => exact absurd (roleOK_phi hok hw hρ).1 (fun h => nomatch h)
  | ncEnd i => exact absurd (roleOK_ncEnd hok hw hρ).1 (fun h => nomatch h)
  | tgt i k => exact absurd (roleOK_tgt hok hw hρ).1 (fun h => nomatch h)
  | ncThen i => exact S.t_nc hH hok hw hid hρ hcov
  | wb i =>
    obtain ⟨-, rfl, r', hr', hargs, hn, -, -, e, hty⟩ := roleOK_wb hok hw hρ
    obtain ⟨M, hRM⟩ := hcov
    exact local_wb hH hw hid hρ hr' hRM (then_op hρ rfl hw) hargs (S.mem_held hr') hn hty
  | sel0 i =>
    obtain ⟨-, rfl, hargs, ha, h0, -⟩ := roleOK_sel hok hw (.inl hρ)
    exact local_sel hM (S.wbN8 ha) hw hid hargs ha (.inl ⟨then_op hρ rfl hw, hρ, h0 hρ⟩)
  | sel1 i =>
    obtain ⟨-, rfl, hargs, ha, -, h1⟩ := roleOK_sel hok hw (.inr hρ)
    exact local_sel hM (S.wbN8 ha) hw hid hargs ha (.inr ⟨then_op hρ rfl hw, hρ, h1 hρ⟩)
  | off i =>
    obtain ⟨-, rfl, hargs, hty, ha, r', hr', h0, h8, hlt⟩ := roleOK_off hok hw hρ
    exact local_off hw hid hρ hr' (then_op hρ rfl hw) hargs ha hty h0 h8 hlt
  | bstore i =>
    obtain ⟨-, rfl, hargs, hty, haux, ho, -, hmm⟩ := roleOK_bstore hok hw hρ
    exact local_bstore hw hid hρ (then_op hρ rfl hw) hargs ho hmm haux hty
  | tload i =>
    exact local_true hw (by rw [then_op hρ rfl hw]; decide) (fun y => by simp only [QR, hρ])
  | none => exact (roleOK_none hok hρ).elim

end Setup

end GoFV.Proof.WB
