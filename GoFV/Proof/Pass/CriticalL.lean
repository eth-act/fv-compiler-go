import GoFV.Proof.Pass.DeadRelL
import GoFV.Proof.SimL
import GoFV.Proof.FrameL
import GoFV.Proof.CongL
import GoFV.Proof.CheckFacts
import GoFV.Opt.Critical

variable [GoFV.SSA.Sem.Addrs]

/-!
# critical refines its input (`runL`, checked)

`critical` (`GoFV/Opt/Critical.lean`, #403) splits critical edges: an edge `p → b` becomes
`p → d → b` through a new empty `Plain` block `d` (several edges whose `Phi` argument is the same
value may share one `d`, which then drops `b`'s predecessors and `Phi` arguments; a shared `d`
with several non-`Plain` predecessors is split in turn, giving `p → d' → d → b`). Nothing else
changes: the values are those of the input (a `Phi` may lose arguments), every input block keeps
its kind, controls, values and auxint, and its successors are the same blocks or chains of
splitters to them (`SplitReach`).

`CritRel f g` states this; `critRelB f g` decides it (`critRelB_sound`). A run of `g` is a run
of `f` with equal frames at block entries, where the target passes through the splitters (block
entries that read and write nothing): a macro-step simulation (`runLoopL_simIH`),
`refinesL_of_critRel`. `critical_refinesL`: the pass's output refines its input when `critRelB`
accepts it (a checked wrapper; `GoFVTest/CriticalProbe.lean` measures the coverage).
-/

namespace GoFV.Proof.Crit

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.Dead GoFV.Opt

attribute [local irreducible] schedule kahn schedValid

/-- A value without position, use count and, for a `Phi`, arguments. -/
def eraseA (v : Value) : Value :=
  { v with pos := default, uses := 0, args := if v.op == .Phi then #[] else v.args }

/-- Block `d` of `g` is a splitter: an empty `Plain` block with its own ID. -/
def Split (g : Func) (d : ID) (db : Block) : Prop :=
  g.block? d = some db ∧ db.id = d ∧ db.kind = .Plain ∧ db.values = #[]

/-- Target edge `e1` reaches target edge `e2` through splitters (a splitter that is later split
itself, as a shared splitter with several non-`Plain` predecessors is, gives a chain). -/
inductive SplitReach (g : Func) : Edge → Edge → Prop
  | refl (e : Edge) : SplitReach g e e
  | step {e1 e2 e3 : Edge} {db : Block} : Split g e1.b db → db.succs[0]? = some e2 →
      SplitReach g e2 e3 → SplitReach g e1 e3

/-- The source edge `e` becomes the target edge `e'`: through splitters, an edge to the same
block with `Phi` arguments read alike. -/
def EdgeOK (f g : Func) (e e' : Edge) : Prop :=
  ∃ e'', SplitReach g e' e'' ∧ e''.b = e.b ∧ PhiArgs f g e.b e.i e''.i

/-- A source block `fb` and its target `gb`. -/
structure BlockRel (f g : Func) (fb gb : Block) : Prop where
  kind : gb.kind = fb.kind
  controls : gb.controls = fb.controls
  values : gb.values = fb.values
  auxInt : gb.auxInt = fb.auxInt
  id : gb.id = fb.id
  succ : ∀ (k : Nat) (e : Edge), fb.succs[k]? = some e → ∃ e', gb.succs[k]? = some e' ∧ EdgeOK f g e e'

/-- What `critical` changes. -/
structure CritRel (f g : Func) : Prop where
  entry : g.entry = f.entry
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  low : g.lowered = f.lowered
  value : ∀ x, (g.value? x).map eraseA = (f.value? x).map eraseA
  block : ∀ bid fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧ BlockRel f g fb gb
  entryPhi : PhiArgs f g f.entry 0 0

/-! ## The checker -/

/-- `PhiArgs`, decided. -/
def phiArgsB (f g : Func) (c : ID) (iS iT : Nat) : Bool :=
  match g.block? c with
  | none => true
  | some gc => gc.values.all fun x =>
    match g.value? x with
    | some gv =>
      if gv.op == .Phi then
        match f.value? x with
        | some fv => gv.args[iT]? == fv.args[iS]?
        | none => false
      else true
    | none => true

/-- `SplitReach` to an edge related to `e`, following at most `n` splitters. -/
def reachB (f g : Func) (e : Edge) : Nat → Edge → Bool
  | 0, _ => false
  | n + 1, e' =>
    (e'.b == e.b && phiArgsB f g e.b e.i e'.i) ||
      match g.block? e'.b with
      | some db =>
        db.id == e'.b && db.kind == .Plain && db.values.isEmpty &&
          match db.succs[0]? with
          | some e'' => reachB f g e n e''
          | none => false
      | none => false

/-- `EdgeOK`, decided (a chain of splitters visits distinct blocks). -/
def edgeOKB (f g : Func) (e e' : Edge) : Bool := reachB f g e (g.blockTab.size + 1) e'

/-- `BlockRel`, decided. -/
def blockRelB (f g : Func) (fb gb : Block) : Bool :=
  gb.kind == fb.kind && gb.controls == fb.controls && gb.values == fb.values &&
    gb.auxInt == fb.auxInt && gb.id == fb.id &&
    (List.range fb.succs.size).all fun k =>
      match fb.succs[k]?, gb.succs[k]? with
      | some e, some e' => edgeOKB f g e e'
      | _, _ => false

/-- `CritRel`, decided. -/
def critRelB (f g : Func) : Bool :=
  g.entry == f.entry && g.ownAux == f.ownAux && g.valueTab.size == f.valueTab.size &&
    g.lowered == f.lowered &&
    ((List.range (max f.valueTab.size g.valueTab.size)).all fun x =>
      (g.value? x).map eraseA == (f.value? x).map eraseA) &&
    ((List.range f.blockTab.size).all fun bid =>
      match f.block? bid with
      | none => true
      | some fb =>
        match g.block? bid with
        | some gb => blockRelB f g fb gb
        | none => false) &&
    phiArgsB f g f.entry 0 0

theorem phiArgsB_sound {f g : Func} {c : ID} {iS iT : Nat} (h : phiArgsB f g c iS iT = true) :
    PhiArgs f g c iS iT := by
  intro gc hgc x hx gv hgv hph
  unfold phiArgsB at h
  rw [hgc] at h
  have := Array.all_eq_true.1 h
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
  have hk' := this k hk
  simp only [hgv, hph, beq_self_eq_true, ite_true] at hk'
  cases hfv : f.value? gc.values[k] with
  | none => rw [hfv] at hk'; cases hk'
  | some fv => rw [hfv] at hk'; exact ⟨fv, rfl, by simpa using hk'⟩

theorem reachB_sound {f g : Func} {e : Edge} :
    ∀ {n : Nat} {e' : Edge}, reachB f g e n e' = true → EdgeOK f g e e'
  | 0, _, h => by cases h
  | n + 1, e', h => by
    unfold reachB at h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨e', .refl e', h.1, phiArgsB_sound h.2⟩
    · split at h
      · rename_i db hdb
        simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h
        obtain ⟨⟨⟨hid, hk⟩, hv⟩, hs⟩ := h
        split at hs
        · rename_i e'' he''
          obtain ⟨e3, hr, hb, hP⟩ := reachB_sound hs
          exact ⟨e3, .step ⟨hdb, hid, hk, hv⟩ he'' hr, hb, hP⟩
        · cases hs
      · cases h

theorem edgeOKB_sound {f g : Func} {e e' : Edge} (h : edgeOKB f g e e' = true) :
    EdgeOK f g e e' :=
  reachB_sound h

theorem blockRelB_sound {f g : Func} {fb gb : Block} (h : blockRelB f g fb gb = true) :
    BlockRel f g fb gb := by
  unfold blockRelB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hk, hc⟩, hv⟩, ha⟩, hid⟩, hs⟩ := h
  refine ⟨hk, hc, hv, ha, hid, fun k e he => ?_⟩
  have hk' := hs k (Array.getElem?_eq_some_iff.1 he).1
  rw [he] at hk'
  cases he' : gb.succs[k]? with
  | none => rw [he'] at hk'; cases hk'
  | some e' => rw [he'] at hk'; exact ⟨e', rfl, edgeOKB_sound hk'⟩

theorem value?_none_of_size {f : Func} {x : ID} (h : f.valueTab.size ≤ x) : f.value? x = none := by
  simp [Func.value?, Array.getElem?_eq_none h]

theorem block?_none_of_size {f : Func} {x : ID} (h : f.blockTab.size ≤ x) : f.block? x = none := by
  simp [Func.block?, Array.getElem?_eq_none h]

/-- **The checker decides `CritRel`.** -/
theorem critRelB_sound {f g : Func} (h : critRelB f g = true) : CritRel f g := by
  unfold critRelB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨he, ho⟩, hs⟩, hl⟩, hv⟩, hb⟩, hp⟩ := h
  refine ⟨he, ho, hs, hl, fun x => ?_, fun bid fb hfb => ?_, phiArgsB_sound hp⟩
  · rcases Nat.lt_or_ge x (max f.valueTab.size g.valueTab.size) with hx | hx
    · exact hv x hx
    · rw [value?_none_of_size (by omega), value?_none_of_size (f := f) (by omega)]
  · have hlt : bid < f.blockTab.size := by
      rcases Nat.lt_or_ge bid f.blockTab.size with h | h
      · exact h
      · rw [block?_none_of_size h] at hfb; cases hfb
    have := hb bid hlt
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb => rw [hgb] at this; exact ⟨gb, rfl, blockRelB_sound this⟩

/-! ## Equal evaluation of related blocks -/

variable {f g : Func}

theorem eraseA_op {u v : Value} (h : eraseA u = eraseA v) : u.op = v.op := by
  have := congrArg Value.op h; exact this

theorem eraseA_eq {u v : Value} (h : eraseA u = eraseA v) :
    u.id = v.id ∧ u.op = v.op ∧ u.type = v.type ∧ u.aux = v.aux ∧ u.auxInt = v.auxInt ∧
      (u.op ≠ .Phi → u.args = v.args) := by
  have hop := eraseA_op h
  refine ⟨by have := congrArg Value.id h; exact this, hop,
    by have := congrArg Value.type h; exact this, by have := congrArg Value.aux h; exact this,
    by have := congrArg Value.auxInt h; exact this, fun hne => ?_⟩
  have := congrArg Value.args h
  simp only [eraseA, hop] at this
  have hne' : (v.op == .Phi) = false := by rw [← hop]; simpa using hne
  simpa [hne'] using this

/-- Related values: both absent, or present with equal `eraseA`. -/
theorem value_rel (R : CritRel f g) (x : ID) :
    (f.value? x = none ∧ g.value? x = none) ∨
      ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧ eraseA gv = eraseA fv := by
  have h := R.value x
  cases hf : f.value? x <;> cases hg : g.value? x <;> simp_all

theorem schedNodes_rel (R : CritRel f g) {fb gb : Block} (hv : gb.values = fb.values) :
    schedNodes g gb = schedNodes f fb := by
  unfold schedNodes
  rw [hv]
  congr 1
  funext id
  rcases value_rel R id with ⟨h1, h2⟩ | ⟨fv, gv, h1, h2, he⟩
  · rw [h1, h2]
  · rw [h1, h2]
    obtain ⟨hid, hop, -, -, -, hargs⟩ := eraseA_eq he
    simp only [hop, hid]
    split
    · rfl
    · rename_i hne
      rw [hargs (by rw [hop]; simpa using hne)]

theorem schedule_rel (R : CritRel f g) {fb gb : Block} (hv : gb.values = fb.values) :
    schedule g gb = schedule f fb := by
  unfold schedule; rw [schedNodes_rel R hv]

theorem tys_rel (R : CritRel f g) (tabs : Tables) :
    (Ctx.makeL tabs g).tys = (Ctx.makeL tabs f).tys := by
  rw [tys_makeL, tys_makeL, R.low]
  have hvt : g.valueTab.map (Option.map eraseA) = f.valueTab.map (Option.map eraseA) := by
    apply Array.ext (by simp [R.vsize])
    intro i h1 h2
    simp only [Array.size_map] at h1 h2
    simp only [Array.getElem_map]
    have := R.value i
    simp only [Func.value?, Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2,
      Option.join_some] at this
    exact this
  exact map_eq_of_factor (H := valueTy _) (fun o => by cases o <;> rfl)
    (fun o => by cases o <;> rfl) hvt

theorem params_rel (R : CritRel f g) (tabs : Tables) :
    (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params := by
  rw [params_makeL, params_makeL]; exact params_make tabs R.ownAux

theorem sxOf_rel (R : CritRel f g) {fv gv : Value} (hargs : gv.args = fv.args) :
    sxOf g gv = sxOf f fv := by
  unfold sxOf
  rw [hargs]
  cases fv.args[0]? with
  | none => rfl
  | some a =>
    simp only [Option.bind_some]
    rcases value_rel R a with ⟨h1, h2⟩ | ⟨fa, ga, h1, h2, he⟩
    · rw [h1, h2]; rfl
    · rw [h1, h2]
      simp only [Option.map_some, Option.some.injEq]
      obtain ⟨-, hop, -, -, -, hargs'⟩ := eraseA_eq he
      refine Arm64.signExtendsIn_congr hop fun hs => ?_
      have hnp : ga.op ≠ .Phi := by rcases hs with h | h <;> rw [h] <;> decide
      rw [hargs' hnp]
      cases fa.args[0]? with
      | none => rfl
      | some c =>
        simp only [Option.bind_some]
        rcases value_rel R c with ⟨h3, h4⟩ | ⟨fc, gc, h3, h4, hec⟩
        · rw [h3, h4]
        · rw [h3, h4]; simp only [Option.map_some, eraseA_op hec]

/-- A source value of a block, other than a `Phi`, evaluates in the target as in the source. -/
theorem evalValueL_rel (R : CritRel f g) {md : LMode} {env : Env} {tabs : Tables} {fr : Frame}
    {fv gv : Value} (he : eraseA gv = eraseA fv) (hne : fv.op ≠ .Phi) :
    evalValueL md env (Ctx.makeL tabs g) fr gv = evalValueL md env (Ctx.makeL tabs f) fr fv := by
  obtain ⟨hid, hop, -, haux, hai, hargs⟩ := eraseA_eq he
  have hargs' := hargs (hop ▸ hne)
  have hsx : sxOf (Ctx.makeL tabs g).f gv = sxOf (Ctx.makeL tabs f).f fv := by
    rw [makeL_f, makeL_f]; exact sxOf_rel R hargs'
  have hc := fun (fa : Bool) (argv : List Val) (ty : Ty) =>
    evalOpL_congr (faulting := fa) (env := env) (fr := fr) (argv := argv) (ty := ty)
      (ctx := Ctx.makeL tabs f) (ctx' := Ctx.makeL tabs g) hop haux hai hid
      (by rw [tabs_makeL, tabs_makeL]) (params_rel R tabs) (by rw [act_makeL, act_makeL]; rfl) hsx
  unfold evalValueL
  rw [hargs', hid, tys_rel R tabs]
  simp only [hc]

/-! ## Block entries -/

/-- A result with its `stuck` message erased (the messages name edge indices, which differ). -/
private def erS {α : Type} : Res α → Res α
  | .stuck _ => .stuck ""
  | r => r

private theorem erS_bind {α β : Type} {a a' : Res α} {k k' : α → Res β} (ha : erS a = erS a')
    (hk : ∀ y, erS (k y) = erS (k' y)) : erS (a >>= k) = erS (a' >>= k') := by
  cases a <;> cases a' <;> simp only [erS, reduceCtorEq, Res.ok.injEq, Res.panic.injEq] at ha <;>
    first
    | (obtain rfl := ha; exact hk _)
    | (obtain ⟨rfl, rfl⟩ := ha; rfl)
    | rfl

private theorem erS_ok {α : Type} {a : Res α} {x : α} (h : erS a = .ok x) : a = .ok x := by
  cases a <;> first | exact h | cases h

private theorem erS_panic {α : Type} {a : Res α} {e : Panic} {m : Mem} (h : erS a = .panic e m) :
    a = .panic e m := by
  cases a <;> first | exact h | cases h

/-- A source value's `Phi` step reads in the target what it reads in the source. -/
private theorem phiStepL_rel (R : CritRel f g) {md : LMode} {tabs : Tables} {fr : Frame} {b : ID}
    {gb : Block} (hgb : g.block? b = some gb) {iS iT : Nat} (hP : PhiArgs f g b iS iT) {z : ID}
    (hz : z ∈ gb.values) :
    erS (phiStepL md (Ctx.makeL tabs g) fr iT z) = erS (phiStepL md (Ctx.makeL tabs f) fr iS z) := by
  unfold phiStepL
  rw [makeL_f, makeL_f, tys_rel R tabs]
  rcases value_rel R z with ⟨h1, h2⟩ | ⟨fv, gv, h1, h2, he⟩
  · rw [h1, h2]
  · rw [h1, h2]
    simp only [eraseA_op he]
    split
    · rename_i hph
      obtain ⟨fv', hfv', ha⟩ := hP gb hgb z hz gv h2 (by rw [eraseA_op he]; simpa using hph)
      rw [h1] at hfv'; cases hfv'
      rw [ha]
      cases fv.args[iS]? with
      | none => rfl
      | some a => rfl
    · rfl

private theorem filterMapM_erS {α β : Type} {F G : α → Res (Option β)} :
    ∀ {l : List α}, (∀ a ∈ l, erS (F a) = erS (G a)) → erS (l.filterMapM F) = erS (l.filterMapM G)
  | [], _ => rfl
  | a :: l, h => by
    have ih := filterMapM_erS (F := F) (G := G) (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.filterMapM_cons, List.filterMapM_cons]
    refine erS_bind (h a List.mem_cons_self) fun o => ?_
    cases o with
    | none => exact ih
    | some p => exact erS_bind ih fun _ => rfl

/-- Scheduled source values evaluate in the target as in the source. -/
private theorem evalAllL_rel (R : CritRel f g) {md : LMode} {env : Env} {tabs : Tables} :
    ∀ {l : List ID}, (∀ x ∈ l, ∃ fv, f.value? x = some fv ∧ fv.op ≠ .Phi) → ∀ fr,
      evalAllL md env (Ctx.makeL tabs g) fr l = evalAllL md env (Ctx.makeL tabs f) fr l
  | [], _, _ => rfl
  | x :: l, h, fr => by
    obtain ⟨fv, hfv, hne⟩ := h x List.mem_cons_self
    have ih := evalAllL_rel R (md := md) (env := env) (tabs := tabs) (l := l)
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    rcases value_rel R x with ⟨h1, -⟩ | ⟨fv', gv, h1, h2, he⟩
    · rw [hfv] at h1; cases h1
    rw [hfv] at h1; cases h1
    simp only [evalAllL, makeL_f, hfv, h2, evalValueL_rel R he hne, ih]

/-- Entering a related block: the same result (up to `stuck` messages). -/
private theorem enter_rel (R : CritRel f g) {md : LMode} {env : Env} {tabs : Tables} {fr : Frame}
    {b : ID} {fb gb : Block} (hown : ValuesOwn f fb) (hfb : f.block? b = some fb)
    (hgb : g.block? b = some gb) (hid : fb.id = b) (B : BlockRel f g fb gb) {iS iT : Nat}
    (hP : PhiArgs f g b iS iT) :
    erS (enterBlockL md env (Ctx.makeL tabs g) fr gb iT) =
      erS (enterBlockL md env (Ctx.makeL tabs f) fr fb iS) := by
  have hph := filterMapM_erS (l := gb.values.toList) fun z hz =>
    phiStepL_rel (md := md) (tabs := tabs) (fr := fr) R hgb hP (Array.mem_toList_iff.1 hz)
  rw [B.values] at hph
  rw [enterBlockL_eq, enterBlockL_eq, B.values, B.id, hid, sched_of_blockL hgb,
    sched_of_blockL hfb, schedule_rel R B.values]
  refine erS_bind hph fun ps => ?_
  cases hs : schedule f fb with
  | none => rfl
  | some o =>
    show erS (evalAllL md env (Ctx.makeL tabs g) _ o.toList) =
      erS (evalAllL md env (Ctx.makeL tabs f) _ o.toList)
    rw [evalAllL_rel R (fun x hx => ?_)]
    obtain ⟨-, v, hv, hne⟩ := (((schedule_spec hs).topo.mem x).1 hx |> (nodeIn_schedNodes hown).1)
    exact ⟨v, hv, hne⟩

/-- An empty block's schedule is empty. -/
private theorem schedule_empty {db : Block} (h : db.values = #[]) : schedule g db = some #[] := by
  have hn : schedNodes g db = #[] := by unfold schedNodes; rw [h]; rfl
  unfold schedule; rw [hn]; decide +kernel

/-- A splitter continues along its successor with the frame unchanged. -/
private theorem split_step {md : LMode} {env : Env} {tabs : Tables} {fr : Frame} {d : ID}
    {db : Block} (hs : Split g d db) {e : Edge} (he : db.succs[0]? = some e) (i : Nat) :
    blockStepL md env (Ctx.makeL tabs g) fr d i = .goto fr e := by
  obtain ⟨hdb, hid, hk, hv⟩ := hs
  have hen : enterBlockL md env (Ctx.makeL tabs g) fr db i = .ok fr := by
    rw [enterBlockL_eq, hv, hid, sched_of_blockL hdb, schedule_empty hv]; rfl
  have hst : stepTermL fr db = .ok (.goto e) := by
    rw [stepTermL_generic fr (by rw [hk]; rfl)]
    unfold stepTerm; rw [hk]; unfold succ; rw [he]; rfl
  unfold blockStepL
  simp only [makeL_f, hdb, hen, hst]

/-- The simulation relation: equal frames at the same block, entered along edges whose `Phi`
arguments read alike; the block is listed in the source. -/
private def Rel (f g : Func) (frS : Frame) (bS iS : Nat) (frT : Frame) (bT iT : Nat) : Prop :=
  frT = frS ∧ bT = bS ∧ bS ∈ f.blocks ∧ PhiArgs f g bS iS iT

/-- One source block step of a related state: the target's along the related edge. -/
private theorem step_rel {ce : CheckEnv} (hwf : WF ce f) (R : CritRel f g) {md : LMode}
    {env : Env} {tabs : Tables} {fr : Frame} {b : ID} {iS iT : Nat} (hb : b ∈ f.blocks)
    (hP : PhiArgs f g b iS iT) :
    (∀ G e, blockStepL md env (Ctx.makeL tabs f) fr b iS = .goto G e →
      ∃ e', blockStepL md env (Ctx.makeL tabs g) fr b iT = .goto G e' ∧ EdgeOK f g e e' ∧
        e.b ∈ f.blocks) ∧
    (∀ rs m, blockStepL md env (Ctx.makeL tabs f) fr b iS = .ret rs m →
      blockStepL md env (Ctx.makeL tabs g) fr b iT = .ret rs m) ∧
    (∀ e m, blockStepL md env (Ctx.makeL tabs f) fr b iS = .panic e m →
      blockStepL md env (Ctx.makeL tabs g) fr b iT = .panic e m) := by
  obtain ⟨fb, hfb, hid⟩ := hwf.blockId b hb
  obtain ⟨gb, hgb, B⟩ := R.block b fb hfb
  have hown : ValuesOwn f fb := fun z hz => by
    obtain ⟨v, hv, hvid, -⟩ := hwf.valueId b fb ⟨hb, hfb⟩ z hz
    exact ⟨v, hv, hvid⟩
  have hen := enter_rel (md := md) (env := env) (tabs := tabs) (fr := fr) R hown hfb hgb hid B hP
  unfold blockStepL
  simp only [makeL_f, hfb, hgb]
  cases hE : enterBlockL md env (Ctx.makeL tabs f) fr fb iS with
  | panic e m =>
    rw [erS_panic (hen.trans (by rw [hE]; rfl))]
    exact ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ h => h⟩
  | stuck msg =>
    exact ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  | ok G =>
    rw [erS_ok (hen.trans (by rw [hE]; rfl))]
    simp only
    cases hst : stepTermL G fb with
    | panic e m => exact absurd hst stepTermL_not_panic
    | stuck msg =>
      exact ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
    | ok n =>
      rcases stepTermL_rel (.inl B.kind) B.auxInt B.controls (fun _ _ => rfl) hst with
        ⟨k, e, rfl, hfk, -, hT⟩ | ⟨rs, m, rfl, hT⟩
      · obtain ⟨e', hgk, hok⟩ := B.succ k e hfk
        have hT' : stepTermL G gb = .ok (.goto e') := by rw [hT]; unfold succ; rw [hgk]; rfl
        rw [hT']
        refine ⟨fun G' e0 h => ?_, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
        cases h
        exact ⟨e', rfl, hok, (hwf.succLink b fb ⟨hb, hfb⟩ k e hfk).1⟩
      · rw [hT]
        exact ⟨fun _ _ h => (by cases h), fun _ _ h => h, fun _ _ h => (by cases h)⟩

/-- The target runs through a chain of splitters with its frame unchanged. -/
private theorem reach_run {md : LMode} {env : Env} {tabs : Tables} {G : Frame} {e1 e2 : Edge}
    (hr : SplitReach g e1 e2) : ∃ k, ∀ fuel,
      runLoopL md env (Ctx.makeL tabs g) (fuel + k) G e1.b e1.i =
        runLoopL md env (Ctx.makeL tabs g) fuel G e2.b e2.i := by
  induction hr with
  | refl e => exact ⟨0, fun _ => rfl⟩
  | step hs he _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, fun fuel => ?_⟩
    rw [← Nat.add_assoc, runLoopL_goto (split_step hs he _), hk]

/-- **The macro-step simulation**: a source block entry is one target entry followed by the
splitters on the target's edge. -/
private theorem sim {ce : CheckEnv} (hwf : WF ce f) (R : CritRel f g) {md : LMode} {env : Env}
    {tabs : Tables} :
    ∀ fuel frS bS iS frT bT iT, Rel f g frS bS iS frT bT iT →
      (runLoopL md env (Ctx.makeL tabs f) fuel frS bS iS).Defined →
      ∃ fuelT, LoopRefines Eq (runLoopL md env (Ctx.makeL tabs f) fuel frS bS iS)
        (runLoopL md env (Ctx.makeL tabs g) fuelT frT bT iT) := by
  refine runLoopL_simIH (Rel f g) fun n ih frS bS iS frT bT iT hR hd => ?_
  obtain ⟨rfl, rfl, hb, hP⟩ := hR
  obtain ⟨hgo, hret, hpan⟩ := step_rel (md := md) (env := env) (tabs := tabs) (fr := frT) hwf R hb hP
  cases hS : blockStepL md env (Ctx.makeL tabs f) frT bT iS with
  | goto G e =>
    obtain ⟨e', hT, hok, heb⟩ := hgo G e hS
    rw [runLoopL_goto hS] at hd ⊢
    obtain ⟨e'', hr, hb'', hP''⟩ := hok
    obtain ⟨k, hk⟩ := reach_run (md := md) (env := env) (tabs := tabs) (G := G) hr
    obtain ⟨ft, hft⟩ := ih n (Nat.le_refl n) G e.b e.i G e''.b e''.i ⟨rfl, hb'', heb, hP''⟩ hd
    exact ⟨ft + k + 1, by rw [runLoopL_goto hT, hk]; exact hft⟩
  | ret rs m =>
    exact ⟨0 + 1, by
      rw [runLoopL_ret hS, runLoopL_ret (hret rs m hS)]
      exact .returned (RefinesList.refl rs) (Mem.Refines.refl m)⟩
  | panic e m =>
    exact ⟨0 + 1, by rw [runLoopL_panic hS, runLoopL_panic (hpan e m hS)]; exact .panicked e rfl⟩
  | stuck => exact absurd hd (runLoopL_stuck hS)

private theorem entryFrame_eq' {env : Env} {ctx ctx' : Ctx} (htabs : ctx.tabs = ctx'.tabs)
    (hpt : ctx.paramTys = ctx'.paramTys) (hloc : ctx.locals = ctx'.locals)
    (hact : ctx.act = ctx'.act) (hsize : ctx.f.valueTab.size = ctx'.f.valueTab.size)
    (args : List Val) (mem : Mem) : entryFrame env ctx args mem = entryFrame env ctx' args mem := by
  unfold entryFrame frameMem frameAllocs
  rw [htabs, hpt, hloc, hact, hsize]

private theorem paramTys_makeL' (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).paramTys = (Ctx.make tabs f).paramTys := by
  unfold Ctx.makeL; split <;> rfl

private theorem locals_makeL' (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).locals = (Ctx.make tabs f).locals := by
  unfold Ctx.makeL; split <;> rfl

/-- **Splitting edges through empty `Plain` blocks refines under `runL`**: `g` related to a
well-formed `f` by `CritRel` refines `f`. -/
theorem refinesL_of_critRel {tabs : Tables} {ce : CheckEnv} (hwf : WF ce f) (R : CritRel f g) :
    RefinesL tabs g tabs f := by
  have hentry : ∀ (env : Env) (args : List Val) (mem : Mem),
      entryFrame env (Ctx.makeL tabs g) args mem = entryFrame env (Ctx.makeL tabs f) args mem :=
    fun env args mem => entryFrame_eq' (by rw [tabs_makeL, tabs_makeL])
      (by rw [paramTys_makeL', paramTys_makeL']; simp only [Ctx.make, abiParams, R.ownAux])
      (by rw [locals_makeL', locals_makeL']; simp only [Ctx.make, abiParams, R.ownAux])
      (by rw [act_makeL, act_makeL]; rfl) (by rw [makeL_f, makeL_f]; exact R.vsize) args mem
  have houts : (Ctx.makeL tabs g).outs = (Ctx.makeL tabs f).outs := by
    rw [outs_makeL, outs_makeL]
    simp only [Ctx.make, abiParams, R.ownAux]
  have hdefers : (Ctx.makeL tabs g).defers = (Ctx.makeL tabs f).defers := by
    unfold Ctx.makeL; split <;> split <;> rfl
  intro env args mem fuel hd
  unfold runL runCtxL at hd ⊢
  rw [R.low, params_rel R tabs]
  by_cases hn : (args.length != (Ctx.makeL tabs f).params.size) = true
  · simp only [hn, ite_true] at hd; exact hd.elim
  · simp only [hn, Bool.false_eq_true, ite_false] at hd ⊢
    rw [hentry env args mem, houts, hdefers, act_makeL tabs g, act_makeL tabs f,
      show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl, makeL_f, makeL_f, R.entry]
    rw [makeL_f, act_makeL] at hd
    obtain ⟨ft, hft⟩ := sim hwf R _ _ _ _ _ _ _ ⟨rfl, rfl, hwf.entry, R.entryPhi⟩ (finish_defined hd)
    exact ⟨ft, finish_refines hd hft⟩

/-! ## The pass -/

/-- **critical refines its input under `runL`** when the checker `critRelB` accepts its output. -/
theorem critical_refinesL {penv : PassEnv} {f : Func} {out : PassOut} {ce : CheckEnv}
    (h : criticalPass penv f = .ok out) (hf : check ce f = .ok ())
    (hc : critRelB f out.func = true) : RefinesL out.tables out.func penv.tables f := by
  simp only [criticalPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact refinesL_of_critRel (check_wf hf) (critRelB_sound hc)

end GoFV.Proof.Crit
