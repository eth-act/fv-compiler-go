import GoFV.Proof.Pass.WBBlock
import GoFV.Proof.Pass.WBCall

/-!
# writebarrier: every value of a chain (issue #36)

`Setup`: the static facts about block `b` of `f` and its chain in `g` (`chainRuns?`, `blockOK`).
`Cov`: the source facts a value of the chain needs, by role (a kept non-`Phi` value, a run's
store and a nil check copied: the source evaluated them in the reference frame `Gr`; the `WB`:
the run's memory is a memory; a helper call: the helpers are the runtime's, the run's memory is
a memory and the source evaluated the run's stores, whose address arguments hold words).
`local_seg`/`local_t`: a non-`Phi` value listed in a segment or
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

/-- Non-`Phi` values outside `B` that are arguments of `B`'s non-`Phi` values evaluate in `Gr` (a
kept nil check of a dominating block, a run's nil check). -/
def OutEv (env : Env) (c : WBCheck.Ctx) (B : Block) (Gr : Frame) : Prop :=
  ∀ n, n ∉ B.values → (∃ y ∈ B.values, ∃ u, c.f.value? y = some u ∧ u.op ≠ .Phi ∧ n ∈ u.args) →
    ∀ un, c.f.value? n = some un → un.op ≠ .Phi → Ev env c Gr n

/-- The source facts a value of the chain needs, by role. -/
def Cov (env : Env) (c : WBCheck.Ctx) (rs : List Run) (Gr : Frame) (x : ID) : Prop :=
  match c.roleOf rs x with
  | .held => c.K.getD x false = true → ∀ u, c.f.value? x = some u → u.op ≠ .Phi → Ev env c Gr x
  | .tgt j k => ∃ r s, rs[j]? = some r ∧ r.src[k]? = some s ∧ Ev env c Gr s
  | .ncEnd j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Ev env c Gr n
  | .ncThen j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Ev env c Gr n
  | .wb j => ∃ M, RunMem Gr rs j M
  | .call j => WbHelpers env ∧ (∃ M, RunMem Gr rs j M) ∧
      ∃ r, rs[j]? = some r ∧ ∀ s ∈ r.src, Ev env c Gr s
  | _ => True

/-! ## Roles: the inverse direction -/

private theorem blk_vals {h : Func} {s : ID} {T : Block} (hT : h.block? s = some T) :
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
      · rw [if_neg h5]
        by_cases h6 : ((vals g r.sp.c).contains x && (g.value? x).any (·.op == .Addr)) = true
        · rw [if_pos h6]; rfl
        rw [if_neg h6]; exact roleRun_notRun

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

theorem roleOf_wbaddr_inv {c : WBCheck.Ctx} {rs : List Run} {x : ID}
    (h : c.roleOf rs x = .wbaddr) : c.isWbaddr x = true := by
  rcases roleOf_cases c rs x with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | h2 | h2
  · exact h1
  all_goals rw [h] at h2
  · cases h2
  · cases h2
  · simp [notRun] at h2
  · rcases otherRole_spec h2.symm with h3 | h3 | ⟨h3, -⟩ <;> cases h3

theorem roleOf_const0_inv {c : WBCheck.Ctx} {rs : List Run} {x : ID}
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

private theorem roleOK_none' {c : WBCheck.Ctx} {b : ID} {B : Block} {segs : List ID}
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

theorem lazy_of_wbaddr {c : WBCheck.Ctx} {x : ID} (h : c.isWbaddr x = true) :
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

theorem lazy_of_const0 {c : WBCheck.Ctx} {x : ID} (h : c.isConst0 x = true) :
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
    rw [blk_vals hC] at hx
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
  rw [blk_vals hT] at hx
  exact hall x hx

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

/-- The source nil check of a run (possibly outside `B`) has its ID. -/
private theorem nc_fid (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) {n : ID}
    (hn : r.nc = some n) {u : Value} (hu : c.f.value? n = some u)
    (hsrc : ∀ x ∈ r.src, x ∈ B.values ∧ c.K.getD x false = false) : u.id = n := by
  obtain ⟨-, -, -, -, hnc, -⟩ := runOf_spec (S.runOf hr)
  obtain ⟨x0, v0, a, nv, hx0, hv0, -, ha, hnv, -, -, hid⟩ := hnc n hn
  obtain ⟨ce, hwf⟩ := S.wf
  have hx0B := (hsrc x0 (List.mem_of_getElem? hx0)).1
  obtain ⟨bid, B', hbB', haB'⟩ :=
    hwf.argListed b B x0 v0 ⟨⟨S.hb, S.hB⟩, hx0B, hv0⟩ a (Array.mem_of_getElem? ha)
  obtain ⟨v', hv', hvid, -⟩ := hwf.valueId bid B' hbB' a haB'
  rw [hnv] at hv'; cases hv'
  have han : a = n := hvid.symm.trans hid
  subst han
  rw [hu] at hnv; cases hnv
  exact hid

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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsrc, -⟩ := runOK_spec (S.run hr)
  exact local_nc hH hw hid hu (S.nc_fid hr hn hu hsrc)
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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hmh, -, hsrc, -⟩ := runOK_spec (S.run hr)
  have hmS : mS = r.sp.mem := S.nc_mem hr hn hu hu2 hsrc
  subst hmS
  exact local_nc hH hw hid hu (S.nc_fid hr hn hu hsrc)
    (fun y' hy' => by simp only [QR, hρ]; exact ⟨r, n, hr, hn, hy'⟩) ⟨y, hy, hev⟩ hopu hopw hty
    hu2 hw2 (availIn_spec hav).1 (fun z hq M hM => ⟨M, hH _ _ _ hmh hq hM⟩)

private theorem seg_tgt (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame} (hH : HeldGr c rs Gr)
    {j i k : Nat} {x : ID} {w : Value} (hok : c.roleOK b B (segsOf b rs) rs false j x = true)
    (hw : c.g.value? x = some w) (hid : w.id = x) (hρ : c.roleOf rs x = .tgt i k)
    (hcov : ∃ r s, rs[i]? = some r ∧ r.src[k]? = some s ∧ Ev env c Gr s) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨-, -, r, s, hr, hs, -, ⟨u, w', hu, hw', hop, hty, haux, hai, hsz, hback, hmt, hall⟩,
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
    ⟨y, hy, hev⟩ hopu hop haux hai hty hmt hsz hlastu hlastw ?_ ?_
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
private theorem memHeld (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    c.held r.sp.mem = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := runOK_spec (S.run hr)
  exact h

/-- A source `Zero`/`Move` the source evaluated in a typed frame: its address arguments hold
words. -/
private theorem ev_words {env : Env} {Gr : Frame} (hty : Typed (Ctx.make c.tabs c.f) Gr)
    {s : ID} {u : Value}
    (hu : c.f.value? s = some u) (hev : Ev env c Gr s) (hop : u.op = .Zero ∨ u.op = .Move) :
    ∀ k, k + 1 < u.args.size → ∀ a, u.args[k]? = some a →
      ∃ y, Gr.regs[a]? = some (some y) ∧ WordV y := by
  obtain ⟨u', y0, hu', -, hev'⟩ := hev
  rw [hu] at hu'; cases hu'
  obtain ⟨L, r0, hL, hop0, -⟩ := evalValue_inv hev'
  intro k hk a ha
  obtain ⟨z, hz, hreg⟩ := regsAre_get hL (k := k) (a := a) (by simpa using ha)
  refine ⟨z, hreg, ?_⟩
  have hzt := hty.hasTy hreg
  rcases hop with hop | hop
  · rw [DAE.evalOp_memRoot (.inr (.inl hop))] at hop0
    obtain ⟨a', p, M, M', rfl, hp, -, -⟩ := zero_inv hop hop0
    have hl := regsAre_length hL
    simp only [List.length_cons, List.length_nil, Array.length_toList] at hl
    obtain rfl : k = 0 := by omega
    cases hz
    exact wordV_of_asPtrWord hp hzt
  · rw [DAE.evalOp_memRoot (.inr (.inr (.inl hop)))] at hop0
    obtain ⟨a', b', d, s', bs, M, M', rfl, hd, hs, -, -, -⟩ := move_inv hop hop0
    have hl := regsAre_length hL
    simp only [List.length_cons, List.length_nil, Array.length_toList] at hl
    rcases k with _ | _ | k
    · cases hz; exact wordV_of_asPtrWord hd hzt
    · cases hz; exact wordV_of_asPtrWord hs hzt
    · omega

/-- **A helper call** of the buffer block. -/
private theorem t_call (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame} (hH : HeldGr c rs Gr)
    (htyG : Typed (Ctx.make c.tabs c.f) Gr)
    {j i : Nat} {x : ID} {w : Value} (hok : c.roleOK b B (segsOf b rs) rs true j x = true)
    (hw : c.g.value? x = some w) (hid : w.id = x) (hρ : c.roleOf rs x = .call i)
    (hcov : WbHelpers env ∧ (∃ M, RunMem Gr rs i M) ∧
      ∃ r, rs[i]? = some r ∧ ∀ s ∈ r.src, Ev env c Gr s) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  obtain ⟨-, rfl, hop, hty, r, hr, P⟩ := roleOK_call hok hw hρ
  obtain ⟨hWb, ⟨M, hM⟩, r', hr', hev⟩ := hcov
  rw [hr] at hr'; cases hr'
  have hMr : MemAt Gr r.sp.mem M := by
    obtain ⟨r', hr', h⟩ := hM; rw [hr] at hr'; cases hr'; exact h
  obtain ⟨name, hname, hn⟩ := P.name
  obtain ⟨abi, habi, hps, hlen⟩ := P.abi
  obtain ⟨mm, hmm, hmr⟩ := P.mem
  obtain ⟨s, u, hs, hu, husz, hopu, hdst⟩ := P.src
  have hWv := ev_words htyG hu (hev s hs) (hopu.imp (·.1) (·.1))
  have hsz : 3 ≤ w.args.size ∧ w.args.size ≤ 4 := by
    rcases hopu with ⟨-, h⟩ | ⟨-, h, -⟩ <;> omega
  have hargs : w.args.toList = w.args.toList.dropLast ++ [mm] := by
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 (by rw [Array.getLast?_toList]; exact hmm)
    rw [hys, List.dropLast_concat]
  have hget : ∀ k, k < w.args.size → w.args.toList.dropLast[k]? = some w.args[k]! ∨
      k = w.args.size - 1 := by
    intro k hk
    by_cases hk' : k < w.args.size - 1
    · left
      rw [List.getElem?_dropLast, if_pos (by simpa using hk'), Array.getElem?_toList,
        getElem!_pos w.args k hk, Array.getElem?_eq_getElem hk]
    · right; omega
  refine local_call hWb hw hid hρ hop hty hname hn habi hps hargs
    (by rw [List.length_dropLast, Array.length_toList]; exact hlen) ?_ ?_
  · intro a ha z hq
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    have hkl : k < w.args.size - 1 := by
      have := (List.getElem?_eq_some_iff.1 hk).1
      simpa using this
    have hwk : w.args[k]! = a := by
      rcases hget k (by omega) with h | h
      · rw [hk] at h; exact (Option.some.inj h).symm
      · omega
    rcases k with _ | _ | _ | k
    · rw [← hwk] at hq
      simp only [QR, P.typ] at hq
      obtain ⟨_, rfl⟩ := hq
      exact Ptr.inWindow_zero _
    · rcases hdst with ⟨he, hav⟩ | ⟨hnc, hnr⟩
      · rw [← hwk, he] at hq
        obtain ⟨y, hy, hwy⟩ := hWv 0 (by omega) u.args[0]! (by
          rw [getElem!_pos u.args 0 (by omega)]; exact Array.getElem?_eq_getElem (by omega))
        rw [hH _ z y (availIn_spec hav).1 hq hy]
        exact hwy
      · rw [← hwk] at hq
        simp only [QR, hnr] at hq
        obtain ⟨r', n, hr', hn', hz⟩ := hq
        rw [hr] at hr'; cases hr'
        rw [hnc] at hn'; cases hn'
        obtain ⟨y, hy, hwy⟩ := hWv 0 (by omega) u.args[0]! (by
          rw [getElem!_pos u.args 0 (by omega)]; exact Array.getElem?_eq_getElem (by omega))
        rw [hy] at hz; cases hz
        exact hwy
    · rcases hopu with ⟨-, h3⟩ | ⟨-, -, h2, hav⟩
      · omega
      · rw [← hwk, h2] at hq
        obtain ⟨y, hy, hwy⟩ := hWv 1 (by omega) u.args[1]! (by
          rw [getElem!_pos u.args 1 (by omega)]; exact Array.getElem?_eq_getElem (by omega))
        rw [hH _ z y (availIn_spec hav).1 hq hy]
        exact hwy
    · omega
  · intro z hq
    rcases hmr with rfl | h | h | h
    · obtain rfl := runMem_mem hH hr hM (S.memHeld hr) hq
      exact ⟨r, M, M, hr, hMr, rfl, .inr rfl⟩
    · simp only [QR, h] at hq
      obtain ⟨r', M', m, hr', hM', rfl, hB⟩ := hq
      exact ⟨r', M', m, hr', hM', rfl, .inl ⟨_, hB⟩⟩
    · simp only [QR, h] at hq
      obtain ⟨r', M', m, hr', hM', rfl, hB⟩ := hq
      exact ⟨r', M', m, hr', hM', rfl, .inl ⟨_, hB⟩⟩
    · simp only [QR, h] at hq
      exact hq

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
  | taddr i =>
    obtain ⟨-, -, hop, -, -, hsym, hty⟩ := roleOK_taddr hok hw hρ
    exact local_taddr hw hid hρ hop hsym hty
  | call i => exact absurd (roleOK_call hok hw hρ).1 Bool.false_ne_true
  | seln i => exact absurd (roleOK_seln hok hw hρ).1 Bool.false_ne_true
  | none => exact (roleOK_none' hok hρ).elim

/-- **A value of a buffer block.** -/
theorem local_t (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hH : HeldGr c rs Gr) (hM : MemsGr Gr) (htyG : Typed (Ctx.make c.tabs c.f) Gr)
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
    obtain ⟨-, rfl, hargs, h0, h8, ⟨e, hty⟩, r', hr', ha⟩ := roleOK_wb hok hw hρ
    exact local_wb hH hM hw hid hρ hr' hcov (then_op hρ rfl hw) hargs (S.memHeld hr') ha
      (wbSize_of hw).symm (by omega) hty
  | sel0 i =>
    obtain ⟨-, rfl, hargs, ha, h0, -⟩ := roleOK_sel hok hw (.inl hρ)
    exact local_sel hw hid hargs ha (.inl ⟨then_op hρ rfl hw, hρ, h0 hρ⟩)
  | sel1 i =>
    obtain ⟨-, rfl, hargs, ha, -, h1⟩ := roleOK_sel hok hw (.inr hρ)
    exact local_sel hw hid hargs ha
      (.inr ⟨then_op hρ rfl hw, hρ, h1 hρ, memSize_sel1 hρ hw hargs⟩)
  | off i =>
    obtain ⟨-, rfl, hargs, hty, ha, h0, h8, hlt⟩ := roleOK_off hok hw hρ
    obtain ⟨r', hr', -⟩ := roleOf_then (o := .OffPtr) (j := i) (by rw [hρ]; rfl)
    exact local_off hw hid hρ hr' (then_op hρ rfl hw) hargs ha hty h0 h8 hlt
  | bstore i =>
    obtain ⟨-, rfl, hargs, hty, haux, ho, -, hmm, hgen⟩ := roleOK_bstore hok hw hρ
    exact local_bstore hw hid hρ (then_op hρ rfl hw) hargs ho hmm (memSize_eq hgen)
      ((memSize_bstore hρ hw hargs).trans (memSize_eq hgen).symm) haux hty
  | tload i =>
    exact local_true hw (by rw [then_op hρ rfl hw]; decide) (fun y => by simp only [QR, hρ])
  | taddr i => exact absurd (roleOK_taddr hok hw hρ).1 (fun h => nomatch h)
  | call i => exact S.t_call hH htyG hok hw hid hρ hcov
  | seln i =>
    obtain ⟨-, rfl, hop, hargs, hai, hty, ha⟩ := roleOK_seln hok hw hρ
    exact local_seln hw hid hρ hop hargs hai hty ha
  | none => exact (roleOK_none' hok hρ).elim

end Setup

end GoFV.Proof.WB
