import GoFV.Proof.Gen.G34
import GoFV.Proof.Gen.Spec35

variable [GoFV.SSA.Sem.Addrs]

/-!
# The values G35's upper-bit table changes for beyond G34's (`docs/plans/proofs3.md` §4)

`vk33_keep35`: a value of G33's kinds (`VK33`) that is a pair load or a select of one
(`pairOp35`), or a narrow load with an entry (`ldEntry35`), runs as its slice's step, after which
G35's table `uStep35` holds when the table before it held (`UOKL`). Each `VKn` (`n` from 33 down
to 2) is a `VK(n-1)` through its `g(n-1)` constructor or one of the slice's new kinds; every kind
other than these names an op outside `ops35` (`ops35_mem`), or, for `Select0`/`Select1` of a
write-barrier request (G8), an argument that is no `LDP` (`sel_wb_pair`).

- `LDP` (G4's `g4_ldp`, G6's `g6_ldp`, G22's `g22_ldp`) writes the X registers of its pair home
  (`PairW`), so the entries of the other registers stay true (`uokl_pair`).
- `Select0`/`Select1` of an `LDP` (G4's `g4_sel`) keeps every X register (`uokl_filter_x`).
- A narrow load (G3's `g3_loadW`, G6's `g6_load`) writes the zero or sign extension of the loaded
  bytes to its register's X register (`uok_ldW`), and keeps the others (`uokl_ld`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The table -/

/-- What `ldEntry35` gave. -/
theorem ldEntry35_spec {lc : LocCtx} {v : Value} {r c : Nat} {sg : Bool}
    (h : ldEntry35 lc v = some (r, c, sg)) :
    ∃ as n, loadOp? v.op = some (as, n, sg) ∧ regHome? lc v.id = some r ∧
      cls (lc.ty v.id) = some c ∧ (c = 8 ∨ c = 16 ∨ c = 32) ∧ 8 * n ≤ c := by
  unfold ldEntry35 at h
  split at h
  · rename_i as n sg' r' c' hl hr hc
    split at h
    · rename_i hcc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcc
      refine ⟨as, n, hl, hr, hc, ?_, hcc.2⟩
      rcases hcc.1.2 with (h | h) | h <;> simp [h]
    · cases h
  · cases h

theorem ldEntry35_none {lc : LocCtx} {v : Value} (h : loadOp? v.op = none) :
    ldEntry35 lc v = none := by
  simp [ldEntry35, h]

/-- The table across a narrow load with an entry. -/
theorem uStep35_ld {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    {e : Nat × Nat × Bool} (h : ldEntry35 lc v = some e) :
    uStep35 lc L v = e :: L.filter (·.1 != e.1) := by
  simp [uStep35, h]

/-- The table across `LDP`: the entries of the registers other than its pair's. -/
theorem uStep35_ldp {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op = .ARM64LDP) :
    uStep35 lc L v = L.filter (!(homeRegs lc v.id).contains ·.1) := by
  have h0 : ldEntry35 lc v = none := ldEntry35_none (by rw [hop]; rfl)
  simp [uStep35, h0, pairOp35, wEntries35, hop]

/-- The table across a select of a pair or acquire load (`pairOp35`): unchanged. -/
theorem uStep35_sel {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (h0 : ldEntry35 lc v = none) (hp : pairOp35 lc v = true)
    (hs : v.op = .Select0 ∨ v.op = .Select1) : uStep35 lc L v = L := by
  rcases hs with h | h <;> simp [uStep35, h0, hp, h]

/-- The table across any other value of `pairOp35`: the entries of a word pair load
(`wEntries35`), and those of the registers other than the home's. -/
theorem uStep35_pairW {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (h0 : ldEntry35 lc v = none) (hp : pairOp35 lc v = true)
    (hs : v.op ≠ .Select0 ∧ v.op ≠ .Select1) :
    uStep35 lc L v =
      wEntries35 v.op (homeRegs lc v.id) ++ L.filter (!(homeRegs lc v.id).contains ·.1) := by
  simp [uStep35, h0, hp, hs.1, hs.2]

/-- The table across a value of `pairOp35` that is no select and no word pair load (an acquire
load, or an op writing only its register): the entries of the registers other than the home's. -/
theorem uStep35_keepOp {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (h0 : ldEntry35 lc v = none) (hp : pairOp35 lc v = true)
    (hs : v.op ≠ .Select0 ∧ v.op ≠ .Select1) (hw : v.op ≠ .ARM64LDPW ∧ v.op ≠ .ARM64LDPSW) :
    uStep35 lc L v = L.filter (!(homeRegs lc v.id).contains ·.1) := by
  rw [uStep35_pairW h0 hp hs]
  simp [wEntries35, hw.1, hw.2]

/-- The table across any other value: G34's step. -/
theorem uStep35_other {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (h0 : ldEntry35 lc v = none) (hp : pairOp35 lc v = false) :
    uStep35 lc L v = uStep34 lc L v := by
  simp [uStep35, h0, hp]

/-- The ops of `pairOp35` that write only their register home (G36's register shifts, G37's ops,
G51b's `SBFIZ`). -/
def keepOps35 : List Op :=
  [.ARM64SLL, .ARM64SRL, .ARM64SRA, .ARM64UMULH, .ARM64MULH, .ARM64UDIV, .ARM64DIV, .ARM64MULW,
    .ARM64UDIVW, .ARM64DIVW, .ARM64UMULL, .ARM64RBIT, .ARM64REVW, .ARM64REV16W, .ARM64MADD,
    .ARM64MSUB, .ARM64MADDW, .ARM64MSUBW, .ARM64SBFX, .ARM64SBFIZ]

/-- The table across an op of `keepOps35`: the entries of the registers other than the home's. -/
theorem uStep35_keepOps {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op ∈ keepOps35) :
    uStep35 lc L v = L.filter (!(homeRegs lc v.id).contains ·.1) := by
  simp only [keepOps35, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    exact uStep35_keepOp (ldEntry35_none (by rw [h]; rfl)) (by simp [pairOp35, h])
      (by simp [h]) (by simp [h])

/-- The ops of the values `vk33_keep35` runs (`pairOp35`'s and the narrow loads). -/
def ops35 : List Op :=
  [.ARM64LDP, .ARM64LDPW, .ARM64LDPSW, .ARM64LDAR, .ARM64LDARW, .ARM64LDARB, .Select0, .Select1,
    .ARM64MOVBload, .ARM64MOVBUload, .ARM64MOVHload, .ARM64MOVHUload, .ARM64MOVWload,
    .ARM64MOVWUload, .ARM64SLL, .ARM64SRL, .ARM64SRA, .ARM64UMULH, .ARM64MULH, .ARM64UDIV,
    .ARM64DIV, .ARM64MULW, .ARM64UDIVW, .ARM64DIVW, .ARM64UMULL, .ARM64RBIT, .ARM64REVW,
    .ARM64REV16W, .ARM64MADD, .ARM64MSUB, .ARM64MADDW, .ARM64MSUBW, .ARM64SBFX, .ARM64SBFIZ]

/-- A value of `pairOp35`, or a narrow load with an entry, has an op of `ops35`. -/
theorem ops35_mem {lc : LocCtx} {v : Value} (hk : pairOp35 lc v = true ∨ ldEntry35 lc v ≠ none) :
    v.op ∈ ops35 := by
  rcases hk with hk | hk
  · refine Classical.byContradiction fun hn => ?_
    simp only [ops35, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp [pairOp35, hn] at hk
  · obtain ⟨⟨r, c, sg⟩, he⟩ := Option.ne_none_iff_exists'.1 hk
    obtain ⟨as, n, hl, -, -, hc, hn⟩ := ldEntry35_spec he
    rcases loadOp?_op hl with ⟨h, rfl, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rcases hc with rfl | rfl | rfl <;> omega
    all_goals simp [ops35, h]

/-- A property every op of `ops35` has holds of `o ∈ ops35`. -/
theorem ops35_all {o : Op} {f : Op → Bool} (hall : ops35.all f = true) (h : o ∈ ops35) :
    f o = true :=
  List.all_eq_true.1 hall _ h

/-- A select of a write-barrier request (G8) is no select of a pair or acquire load. -/
theorem sel_wb_pair {lc : LocCtx} {v : Value} {c : ID}
    (hop : v.op = .Select0 ∨ v.op = .Select1) (hp : pairOp35 lc v = true)
    (hc : v.args[0]? = some c) (hw : wbArg lc c = true) : False := by
  simp only [wbArg, Bool.and_eq_true, beq_iff_eq] at hw
  cases hv : lc.ctx.f.value? c with
  | none => rw [hv] at hw; cases hw.1.1
  | some u =>
    rw [hv] at hw
    have hu : u.op = .ARM64LoweredWB := by simpa using hw.1.1
    rcases hop with h | h <;> simp [pairOp35, h, hc, hv, hu] at hp

/-! ## The upper-bit invariant -/

/-- After the machine's narrow load of `n` bytes `Y` into the X register of `r`, the entry
`(r, c, sg)` holds. -/
theorem uok_ldW {m m' : MState} {r c kd n : Nat} {sg : Bool} {Y : BitVec (8 * n)}
    (hor : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + kd)) (hn : 1 ≤ n) (hnc : 8 * n ≤ c)
    (hc : c ≤ 64)
    (hx : m'.x = (m.wX (BitVec.ofNat 5 kd)
      (if sg then ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64)).x) :
    UOK m' (some (r, c, sg)) := by
  intro k hk hobj
  obtain ⟨k0, hk0, hrd0, hk0'⟩ := objOf?_some hor
  have hkk0 : kd = k0 := by omega
  subst hkk0
  rcases hk0' with ⟨hzr, -⟩ | ⟨-, hobj0⟩
  · rw [hzr] at hobj; cases hobj
  · rw [hobj] at hobj0
    have hkk := ofNat5_inj (by omega) (by omega) (Option.some.inj hobj0)
    subst hkk
    rw [hx, wX_x_self hk]
    exact extOK_load sg hn hnc hc Y

/-- Across a write of the X register of `r` after which `(r, c, sg)` holds, the table with that
entry in place of `r`'s. -/
theorem uokl_ld {m m' : MState} {L : List (Nat × Nat × Bool)} {r c kd : Nat} {sg : Bool}
    {val : BitVec 64} (hL : UOKL m L) (hu : UOK m' (some (r, c, sg)))
    (hor : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + kd))
    (hx : m'.x = (m.wX (BitVec.ofNat 5 kd) val).x) :
    UOKL m' ((r, c, sg) :: L.filter (·.1 != r)) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact hu
  · exact uokl_filter hL (keepsX_wX hor hx) e he

/-- Across a pair load, the entries of the registers other than its pair's. -/
theorem uokl_pair {m m' : MState} {L : List (Nat × Nat × Bool)} {ra rb : Nat} (hL : UOKL m L)
    (hp : PairW ra rb m m') : UOKL m' (L.filter (!([ra, rb]).contains ·.1)) := by
  obtain ⟨ka, kb, va, vb, hoa, hob, hx⟩ := hp
  intro e he
  obtain ⟨r', c, sg⟩ := e
  rw [List.mem_filter] at he
  obtain ⟨heL, hne⟩ := he
  have ha : r' ≠ ra := by intro h; subst h; simp at hne
  have hb : r' ≠ rb := by intro h; subst h; simp at hne
  intro k hk31 hobj
  have h1 : KeepsX (m.wX (BitVec.ofNat 5 ka) va) m' rb := keepsX_wX hob hx
  have h2 : KeepsX m (m.wX (BitVec.ofNat 5 ka) va) ra := keepsX_wX hoa rfl
  rw [h1 k hk31 (fun h => hb (objX?_inj hobj h)), h2 k hk31 (fun h => ha (objX?_inj hobj h))]
  exact hL _ heL k hk31 hobj

/-- Across a value that keeps every X register, any part of the table. -/
theorem uokl_filter_x {m m' : MState} {L : List (Nat × Nat × Bool)}
    {p : Nat × Nat × Bool → Bool} (hL : UOKL m L) (hx : m'.x = m.x) : UOKL m' (L.filter p) :=
  fun e he => uok_of_x hx (hL e (List.mem_filter.1 he).1)

/-- Across a value that writes at most its register home's X register (`XW`), the entries of the
registers other than its home's. -/
theorem uokl_xw {lc : LocCtx} {v : Value} {m m' : MState} {L : List (Nat × Nat × Bool)}
    (hL : UOKL m L) (hx : XW lc v m m') :
    UOKL m' (L.filter (!(homeRegs lc v.id).contains ·.1)) := by
  rcases hx with hx | ⟨r, kd, val, hh, hor, hx⟩
  · exact uokl_filter_x hL hx
  · have hr : homeRegs lc v.id = [r] := by simp [homeRegs, hh]
    rw [hr]
    intro e he
    apply uokl_filter hL (keepsX_wX hor hx) e
    simp only [List.mem_filter, List.contains_cons, List.contains_nil, Bool.or_false,
      Bool.not_eq_true'] at he
    simp only [List.mem_filter, bne_iff_ne, ne_eq]
    refine ⟨he.1, fun h => ?_⟩
    simp [h] at he

/-- Across a write of the X register of `r` alone, the entries of the other registers. -/
theorem uokl_one {m m' : MState} {L : List (Nat × Nat × Bool)} {r kd : Nat} {val : BitVec 64}
    (hL : UOKL m L) (hor : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + kd))
    (hx : m'.x = (m.wX (BitVec.ofNat 5 kd) val).x) :
    UOKL m' (L.filter (!([r]).contains ·.1)) := by
  intro e he
  apply uokl_filter hL (keepsX_wX hor hx) e
  simp only [List.mem_filter, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.not_eq_true'] at he
  simp only [List.mem_filter, bne_iff_ne, ne_eq]
  refine ⟨he.1, fun h => ?_⟩
  simp [h] at he

/-- `m'` is `m` after a word pair load into the X registers of `ra` and `rb`: `LDPW` (`sg` false)
zero-, `LDPSW` sign-extending a word into each. -/
def WPairW (ra rb : Nat) (sg : Bool) (m m' : MState) : Prop :=
  ∃ (ka kb : Nat) (Y0 Y1 : BitVec (8 * 4)), objOf? ra = some (GoFV.Asm.ARM64.REG_R0 + ka) ∧
    objOf? rb = some (GoFV.Asm.ARM64.REG_R0 + kb) ∧
    m'.x = ((m.wX (BitVec.ofNat 5 ka)
      (if sg then ProgOp.sextTo64 4 (Y0.setWidth 64) else Y0.setWidth 64)).wX (BitVec.ofNat 5 kb)
      (if sg then ProgOp.sextTo64 4 (Y1.setWidth 64) else Y1.setWidth 64)).x

/-- After a word pair load into the X registers of `ra` and `rb` (`WPairW`), their entries and
those of the other registers. -/
theorem uokl_wpair {m m' : MState} {L : List (Nat × Nat × Bool)} {ra rb : Nat} {sg : Bool}
    (hL : UOKL m L) (hne : ra ≠ rb) (hw : WPairW ra rb sg m m') :
    UOKL m' ([ra, rb].map (fun r => (r, 32, sg)) ++ L.filter (!([ra, rb]).contains ·.1)) := by
  obtain ⟨ka, kb, Y0, Y1, hoa, hob, hx⟩ := hw
  intro e he
  rcases List.mem_append.1 he with he | he
  · have h0 : UOK (m.wX (BitVec.ofNat 5 ka)
        (if sg then ProgOp.sextTo64 4 (Y0.setWidth 64) else Y0.setWidth 64)) (some (ra, 32, sg)) :=
      uok_ldW hoa (by decide) (by decide) (by decide) rfl
    have h1 : UOK m' (some (rb, 32, sg)) := uok_ldW hob (by decide) (by decide) (by decide) hx
    have hk : KeepsX (m.wX (BitVec.ofNat 5 ka)
        (if sg then ProgOp.sextTo64 4 (Y0.setWidth 64) else Y0.setWidth 64)) m' rb :=
      keepsX_wX hob hx
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · intro k hk31 hobj
      rw [hk k hk31 (fun h => hne (objX?_inj hobj h))]
      exact h0 k hk31 hobj
    · exact h1
  · exact uokl_pair hL ⟨ka, kb, _, _, hoa, hob, hx⟩ e he

/-! ## The values -/

/-- Refutes `h' : v.op = .X` for an op `.X` outside `ops35`, against `hops : v.op ∈ ops35`. -/
local macro "refute35" hops:ident h':ident : tactic => `(tactic|
  (rw [$h':ident] at $hops:ident; exact absurd $hops (by decide)))

/-- Refutes `h' : f v.op = some _` for an op function `f` that is `none` on `ops35`. -/
local macro "refuteF35" hops:ident h':ident f:term : tactic => `(tactic|
  (have h1 := ops35_all (f := fun o => ($f o).isNone) (by decide) $hops;
   rw [$h':ident] at h1; cases h1))

/-- A narrow load's step, after which G35's table holds: the loaded register's entry, and the
entries of the other registers. -/
theorem ld_uokl {lc : LocCtx} {v : Value} {m m' : MState} {L : List (Nat × Nat × Bool)}
    {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int} {kd : Nat} {Y : BitVec (8 * n)}
    (hk : pairOp35 lc v = true ∨ ldEntry35 lc v ≠ none)
    (hop : loadOp? v.op = some (as, n, sg)) (hro : resObj lc v = .ok (c, rd))
    (hrd : rd = GoFV.Asm.ARM64.REG_R0 + kd)
    (hx : m'.x = (m.wX (BitVec.ofNat 5 kd)
      (if sg then ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64)).x)
    (hL : UOKL m L) : UOKL m' (uStep35 lc L v) := by
  have hnp : pairOp35 lc v = false := by
    rcases loadOp?_op hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      simp [pairOp35, h]
  have he := hk.resolve_left (by rw [hnp]; nofun)
  obtain ⟨⟨r, c', sg'⟩, he⟩ := Option.ne_none_iff_exists'.1 he
  obtain ⟨as', n', hl', hr, hc', hcc, hn⟩ := ldEntry35_spec he
  rw [hop] at hl'
  simp only [Option.some.injEq, Prod.mk.injEq] at hl'
  obtain ⟨rfl, rfl, rfl⟩ := hl'
  obtain ⟨r0, hvh0, -, hor0, -⟩ := resObj_spec hro
  rw [regHome?_eq.2 hvh0] at hr
  cases hr
  rw [hrd] at hor0
  have hn1 : 1 ≤ n := by rcases (loadOp?_bytes hop).1 with h | h | h | h <;> omega
  rw [uStep35_ld he]
  exact uokl_ld hL (uok_ldW hor0 hn1 hn (by omega) hx) hor0 hx

/-- One value of G33's kinds that is a pair load, a select of one, or a narrow load with an entry:
its step, after which G35's table `uStep35` holds when the table before it held. -/
theorem vk33_keep35 {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E)
    (hv : lc.ctx.f.value? id = some v) (hVK : VK33 lc g v kd)
    (hk : pairOp35 lc v = true ∨ ldEntry35 lc v ≠ none)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G14Pre lc s v) (hL : UOKL m L)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' ∧
      UOKL m' (uStep35 lc L v) := by
  obtain ⟨-, -, -, -, -, hglob, -, -, -, -, -⟩ := hE.env.env.env.env
  have hvars := hE.env.env.env.vars
  have hR := kread_of_reads hreads
  have hops := ops35_mem hk
  -- a pair load: the entries of the registers other than its pair's
  have pair : ∀ {ra rb : Nat} (m' : MState), v.op = .ARM64LDP →
      lc.home v.id = some (.pair (some ra) (some rb)) →
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' →
      SlotInv lc s' → PairW ra rb m m' →
      ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' ∧
        UOKL m' (uStep35 lc L v) := by
    intro ra rb m' hop hh h1 h2 h3 h4 h5
    refine ⟨m', h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_ldp hop]
    have hr : homeRegs lc v.id = [ra, rb] := by simp [homeRegs, hh]
    rw [hr]
    exact uokl_pair hL h5
  cases hVK with
  | un h' => refuteF35 hops h' un33?
  | ubfiz h' => refute35 hops h'
  | sra h' => refute35 hops h'
  | cmnw h' => refute35 hops h'
  | g32 _ _ _ _ h32 =>
  cases h32 with
  | bin h' => refuteF35 hops h' bin32?
  | binK h' => refuteF35 hops h' binK32?
  | un h' => refuteF35 hops h' un32?
  | csinc h' => refute35 hops h'
  | stlr h' =>
    have h1 := ops35_all (f := fun o => (stlr? o).isNone) (by decide) hops
    rw [h'] at h1; cases h1
  | g28 _ _ _ _ _ h28 =>
  cases h28 with
  | memEq h' => refute35 hops h'
  | g27 _ h27 =>
  cases h27 with
  | logSh h' =>
    have h1 := ops35_all (f := fun o => (logSh? o).isNone) (by decide) hops
    rw [h'] at h1; cases h1
  | g25 _ h25 =>
  cases h25 with
  | csel h' => refute35 hops h'
  | csel0 h' => refute35 hops h'
  | tst h' => refute35 hops h'
  | tstw h' => refute35 hops h'
  | g24 _ _ h24 =>
  cases h24 with
  | sp h' => refute35 hops h'
  | g23 _ h23 =>
  cases h23 with
  | cset hc =>
    have h1 := ops35_all (f := fun o => !(Cond.ofOp o).isSome) (by decide) hops
    rw [hc] at h1; cases h1
  | g22 _ h22 =>
  cases h22 with
  | ldp hop hx _ _ hsy hsz2 hty h0 h1 h80 h81 hma hh hne hza hzb hda hdb hoa hob =>
    obtain ⟨m', h1', h2', h3', h4', h5'⟩ := g22_ldp (H := H) F hglob hm hinv.core hinv.slots
      (kpair_kStep (by rw [hop]; nofun) hh hty h0 h1 hne) hpre.1.1.1 hj hj' hx hsy hop hsz2 hty
      h0 h1 h80 h81 hma hh hza hzb hda hdb hoa hob hvs htemp hs
    exact pair m' hop hh h1' h2' h3' h4' h5'
  | stp h' => refute35 hops h'
  | g21 _ h21 =>
  cases h21 with
  | regSame h' => refute35 hops h'
  | regMov h' => refute35 hops h'
  | g20 _ h20 =>
  cases h20 with
  | nop h' => refute35 hops h'
  | g19 _ h19 =>
  cases h19 with
  | pb h' =>
    have h1 := ops35_all (f := fun o => !pbOp o) (by decide) hops
    rw [h'] at h1; cases h1
  | g18 _ h18 =>
  cases h18 with
  | stIdx h' => refuteF35 hops h' storeIdxOp?
  | g17 h17 =>
  cases h17 with
  | getG h' => refute35 hops h'
  | g16 h16 =>
  cases h16 with
  | addSh h' => refute35 hops h'
  | g15 h15 =>
  cases h15 with
  | call h' => refute35 hops h'
  | g14 _ h14 =>
  cases h14 with
  | idx h' => refuteF35 hops h' loadIdxOp?
  | g13 h13 =>
  cases h13 with
  | zero h' => refute35 hops h'
  | g12 h12 =>
  cases h12 with
  | conv h' => refute35 hops h'
  | g11 h11 =>
  cases h11 with
  | clo h' => refute35 hops h'
  | g10 h10 =>
  cases h10 with
  | icall h' => refuteF35 hops h' icallLead
  | selMem h' => refute35 hops h'
  | selReg h' => refute35 hops h'
  | g9 h9 =>
  cases h9 with
  | call h' => refute35 hops h'
  | g8 _ h8 =>
  cases h8 with
  | wb h' => refute35 hops h'
  | sel0 hop _ hc hw =>
    exact (sel_wb_pair (.inl hop)
      (hk.resolve_right (by rw [ldEntry35_none (by rw [hop]; rfl)]; nofun)) hc hw).elim
  | sel1 hop _ hc hw =>
    exact (sel_wb_pair (.inr hop)
      (hk.resolve_right (by rw [ldEntry35_none (by rw [hop]; rfl)]; nofun)) hc hw).elim
  | g7 h7 =>
  cases h7 with
  | nil h' => refute35 hops h'
  | g6 _ h6 =>
  cases h6 with
  | var hfv hVar =>
    have hι := var_addr hfv hv hvars
    have hx := hfv.aux
    have hvar := hfv.var
    have hf := hfv.temp
    cases hVar with
    | addr h' => refute35 hops h'
    | load hop hsz2 hma hro hc =>
      obtain ⟨m', h1, h2, h3, h4, kd, Y, hrd, hx'⟩ := g6_load (H := H) F hm hinv.core hinv.slots
        (knext_kStep fun _ => (hs_res hro).noRegs) hpre.1.1.1.1 hj hj' hx hvar hf hι hop hsz2
        hma hro hc hvs htemp hs
      exact ⟨m', h1, h2, ⟨h3, h4⟩, ld_uokl hk hop hro hrd hx' hL⟩
    | store h' => refuteF35 hops h' storeOp?
    | ldp hop hsz2 hty h0 h1 h80 h81 hma hh hne hza hzb hda hdb hoa hob =>
      obtain ⟨m', h1', h2', h3', h4', h5'⟩ := g6_ldp (H := H) F hm hinv.core hinv.slots
        (kpair_kStep (by rw [hop]; nofun) hh hty h0 h1 hne) hpre.1.1.1 hj hj' hx hvar hf hι hop
        hsz2 hty h0 h1 h80 h81 hma hh hza hzb hda hdb hoa hob hvs htemp hs
      exact pair m' hop hh h1' h2' h3' h4' h5'
    | stp h' => refute35 hops h'
  | g5 h5 =>
  cases h5 with
  | mark h' => refuteF35 hops h' markOp?
  | g4 _ h4 =>
  cases h4 with
  | ldp hop hsz2 hax hty h0 h1 h80 h81 hao hma hh hne hza hzb hda hdb hoa hob =>
    obtain ⟨m', h1', h2', h3', h4', h5'⟩ := g4_ldp (H := H) F hm hinv.core hinv.slots hR
      (kpair_kStep (by rw [hop]; nofun) hh hty h0 h1 hne) hpre.1.1.1 hj hj' hop hsz2 hax hty h0
      h1 h80 h81 hao hma hh hza hzb hda hdb hoa hob hvs htemp hs
    exact pair m' hop hh h1' h2' h3' h4' h5'
  | stp h' => refute35 hops h'
  | sel hop hsz1 hc0 _ _ hpt hhc hvh hrz hd hob hcls hcl =>
    obtain ⟨m', h1, h2, h3, h4, hx⟩ := g4_sel (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz1 hc0 hpt hhc hvh hrz hd hob hcl
      (fun c0 hc0' => ksel4_of_reads hreads hop hc0 hhc (hcl.trans hc0')) hvs htemp hs
    have hl0 : loadOp? v.op = none := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
    have hp := hk.resolve_right (by rw [ldEntry35_none hl0]; nofun)
    refine ⟨m', h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_sel (ldEntry35_none hl0) hp (hop.imp And.left And.left)]
    exact fun e he => uok_of_x hx (hL e he)
  | g3 _ _ _ _ h3 =>
  cases h3 with
  | g2 _ _ h2 =>
    cases h2 with
    | g1 _ _ _ _ _ h1 =>
      cases h1 with
      | phi h' => refute35 hops h'
      | zero h' => refute35 hops h'
      | inl h' => refute35 hops h'
      | copyMem h' => refute35 hops h'
      | copySame h' => refute35 hops h'
      | copyMov h' => refute35 hops h'
      | result h' => refute35 hops h'
      | movConst h' => refute35 hops h'
      | alu h' => rcases h' with ⟨h', -⟩ | ⟨h', -⟩ <;> refute35 hops h'
      | aluK h' => rcases h' with ⟨h', -⟩ | ⟨h', -⟩ <;> refute35 hops h'
      | cmp h' => refute35 hops h'
      | cmpK h' => refute35 hops h'
      | load h' => refute35 hops h'
      | store h' => refute35 hops h'
    | call h' => refute35 hops h'
    | selMem h' => refute35 hops h'
    | selReg h' => refute35 hops h'
    | addr h' => refute35 hops h'
    | spill h' => refute35 hops h'
    | reload h' => refute35 hops h'
  | load hop _ hsz2 hacc hma hro hcw hpat =>
    obtain ⟨m', h1, h2, h3, h4, kd, Y, hrd, hx'⟩ := g3_loadW (H := H) F
      (fun y name abi h => hglob y name abi h) hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_res hro).noRegs) hpre.1.1.1.1 hj hj' hop hsz2 hacc hma hro hcw
      hpat hvs htemp hs
    exact ⟨m', h1, h2, ⟨h3, h4⟩, ld_uokl hk hop hro hrd hx' hL⟩
  | store h' => refuteF35 hops h' storeOp?
  | sb h' => refute35 hops h'
  | ext h' => refuteF35 hops h' extOp?
  | aluK h' => rcases h' with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> refute35 hops h'
  | ubfx h' => refute35 hops h'
  | cmpw h' => refute35 hops h'
  | cmpwK h' => refute35 hops h'

end GoFV.Proof.Gen
