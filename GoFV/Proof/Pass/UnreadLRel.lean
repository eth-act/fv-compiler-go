import GoFV.Proof.Pass.DAE
import GoFV.Proof.RetypeL
import GoFV.Opt.ElimUnreadAutos

variable [GoFV.SSA.Sem.Addrs]

/-!
# elim unread autos on `runL`: the checker and its relation

`UnreadL.urel tabs f g` accepts `g` as a result of `elim unread autos` on `f` (translation
validation, `unreadLFrag`): `g` has `f`'s control-flow graph, blocks (kinds, values, controls,
`auxInt`) and values, each kept (`DSE.sameV`) or an eliminated write (`elimV`: a symbol store
`MOV*store`/`FMOV*store`/`STP*` or a `VarDef` became `Copy mem`) to a frame variable of the set
`E` (`names`), and:

* every variable of `E` is a frame temporary the panic machinery does not read
  (`DAE.unforgeable`: a `PAUTO` without the `addrconv` flag, `Blk.temp`; no open-coded defer
  slot or `deferBits`), so an ABIInternal `PPARAM` (a `Blk.local`) is never eliminated here;
* no kept value names a variable of `E` (its aux): nothing reads, addresses or redefines them, so
  no pointer into them ever exists and only the eliminated writes touch them;
* every kept value with a memory- or tuple-shaped argument (at `runL`'s shapes, `shapesL`) has it
  last and an op of `memOpsL` (or is a `Phi`): the proof treats these ops one by one, any other
  value reads equal arguments in source and target;
* `g` is lowered iff `f` is (one `runL` mode for both), and every block's schedule in `g` lists
  `g`'s roots in `f`'s order (`DSE.schedOK`).

`URel` is the declarative form, `urel_sound` reads it off the checker.
-/

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- The writes `elim unread autos` turns into `Copy mem` that the proof covers: the symbol
stores of `arm64Op` and `VarDef`. -/
def elimOps : List Op :=
  [.VarDef, .ARM64MOVBstore, .ARM64MOVHstore, .ARM64MOVWstore, .ARM64MOVDstore,
    .ARM64FMOVSstore, .ARM64FMOVDstore, .ARM64FMOVQstore, .ARM64STP, .ARM64STPW, .ARM64FSTPD,
    .ARM64FSTPS, .ARM64FSTPQ]

/-- `gv` is the eliminated write `fv`: `Copy` of its memory argument. -/
def elimV (fv gv : Value) : Bool :=
  elimOps.contains fv.op && gv.op == .Copy && gv.aux == none && gv.auxInt == 0 &&
    gv.id == fv.id && gv.type == fv.type && gv.block == fv.block &&
    match fv.args.back? with
    | some m => gv.args == #[m]
    | none => false

/-- The eliminated variables: the auxes of the eliminated writes. -/
def names (f g : Func) : List AuxRef :=
  (List.range f.valueTab.size).foldl (fun E x =>
    match f.value? x, g.value? x with
    | some fv, some gv =>
      if elimV fv gv then
        match fv.aux with
        | some n => if E.contains n then E else E ++ [n]
        | none => E
      else E
    | _, _ => E) []

/-- The kept ops beyond `DAE.memOps` whose last argument may be memory-shaped (the proof handles
them on a memory last argument): `SPanchored`, `WBend` and arm64 memory ops. -/
def armMemOps : List Op :=
  [.SPanchored, .WBend,
    -- symbol loads and stores
    .ARM64MOVBload, .ARM64MOVBUload, .ARM64MOVHload, .ARM64MOVHUload, .ARM64MOVWload,
    .ARM64MOVWUload, .ARM64MOVDload, .ARM64FMOVSload, .ARM64FMOVDload, .ARM64FMOVQload,
    .ARM64LDP, .ARM64LDPW, .ARM64LDPSW, .ARM64FLDPD, .ARM64FLDPS, .ARM64FLDPQ,
    .ARM64MOVBstore, .ARM64MOVHstore, .ARM64MOVWstore, .ARM64MOVDstore, .ARM64FMOVSstore,
    .ARM64FMOVDstore, .ARM64FMOVQstore, .ARM64STP, .ARM64STPW, .ARM64FSTPD, .ARM64FSTPS,
    .ARM64FSTPQ,
    -- indexed stores
    .ARM64MOVBstoreidx, .ARM64MOVHstoreidx, .ARM64MOVWstoreidx, .ARM64MOVDstoreidx,
    .ARM64FMOVSstoreidx, .ARM64FMOVDstoreidx, .ARM64MOVHstoreidx2, .ARM64MOVWstoreidx4,
    .ARM64MOVDstoreidx8, .ARM64FMOVSstoreidx4, .ARM64FMOVDstoreidx8,
    -- indexed loads
    .ARM64MOVDloadidx, .ARM64MOVWloadidx, .ARM64MOVWUloadidx, .ARM64MOVHloadidx,
    .ARM64MOVHUloadidx, .ARM64MOVBloadidx, .ARM64MOVBUloadidx, .ARM64FMOVSloadidx,
    .ARM64FMOVDloadidx, .ARM64MOVHloadidx2, .ARM64MOVHUloadidx2, .ARM64MOVWloadidx4,
    .ARM64MOVWUloadidx4, .ARM64MOVDloadidx8, .ARM64FMOVSloadidx4, .ARM64FMOVDloadidx8,
    -- calls, checks, panics, barriers
    .ARM64CALLstatic, .ARM64CALLclosure, .ARM64CALLinter, .ARM64LoweredNilCheck,
    .ARM64LoweredPanicBoundsRR, .ARM64LoweredPanicBoundsRC, .ARM64LoweredPanicBoundsCR,
    .ARM64LoweredPanicBoundsCC, .ARM64LoweredMemEq, .ARM64DMB, .ARM64PRFM,
    -- memory pseudo-ops
    .ARM64LDAR, .ARM64LDARB, .ARM64LDARW, .ARM64LoweredZero, .ARM64LoweredZeroLoop,
    .ARM64LoweredMove, .ARM64LoweredMoveLoop, .ARM64LoweredWB]

/-- The shape of type `t` in `runL`'s context for `f`. -/
def shapeOf (tabs : Tables) (f : Func) (t : TypeRef) : Ty :=
  (shapesL f.lowered tabs)[t]?.getD .other

/-- An argument that is not memory- or tuple-shaped. -/
def plainArg (tabs : Tables) (f : Func) (a : ID) : Bool :=
  match f.value? a with
  | some av => !DAE.memTy (shapeOf tabs f av.type)
  | none => true

/-- The last argument of `fv` is memory-shaped. -/
def memLast (tabs : Tables) (f : Func) (fv : Value) : Bool :=
  match fv.args.back?.bind f.value? with
  | some mv => match shapeOf tabs f mv.type with
    | .mem => true
    | _ => false
  | none => false

/-- Kept value `fv`: no eliminated variable as aux; a memory- or tuple-shaped argument only last
and only for `DAE.memOps` or, on a memory-shaped last argument, `armMemOps` (any for a
`Phi`). -/
def keptOK (tabs : Tables) (f : Func) (E : List AuxRef) (fv : Value) : Bool :=
  !(fv.aux.any E.contains) &&
    (fv.op == .Phi || fv.args.all (plainArg tabs f) ||
      (fv.args.pop.all (plainArg tabs f) &&
        (DAE.memOps.contains fv.op || (armMemOps.contains fv.op && memLast tabs f fv))))

/-- Value `x`: kept, or an eliminated write to a variable of `E`; no value of `g` where `f` has
none. -/
def valueOK (tabs : Tables) (f g : Func) (E : List AuxRef) (x : ID) : Bool :=
  match f.value? x with
  | none => (g.value? x).isNone
  | some fv =>
    match g.value? x with
    | some gv =>
      (DSE.sameV fv gv && keptOK tabs f E fv) || (elimV fv gv && fv.aux.any E.contains)
    | none => false

/-- Block `bid`: the same kind, values, controls and `auxInt`. -/
def blockOK (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.values == fb.values && gb.controls == fb.controls &&
      gb.auxInt == fb.auxInt
  | _, _ => false

/-- **elim unread autos' output relation** (see the module comment). -/
def urel (tabs : Tables) (f g : Func) : Bool :=
  let E := names f g
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
  g.valueTab.size == f.valueTab.size && g.lowered == f.lowered &&
  E.all (DAE.unforgeable tabs) &&
  f.blocks.all (blockOK f g) &&
  (List.range f.valueTab.size).all (valueOK tabs f g E) &&
  f.blocks.all (DSE.schedOK f g)

end GoFV.Proof.UnreadL

namespace GoFV.Opt

/-- `elimUnreadAutos_refinesL`' fragment: the pass fails, changes nothing, or the checker
accepts its result. -/
def unreadLFrag (env : PassEnv) (f : GoFV.SSA.Func) : Bool :=
  match elimUnreadAutosPass env f with
  | .ok out => out.func == f || GoFV.Proof.UnreadL.urel env.tables f out.func
  | .error _ => true

end GoFV.Opt

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- The declarative output relation. -/
structure URel (tabs : Tables) (f g : Func) (E : List AuxRef) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  low : g.lowered = f.lowered
  temp : ∀ n ∈ E, tabs.forgeable n = false
  nodefer : ∀ n ∈ E, DAE.deferVar tabs n = false
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    gb.kind = fb.kind ∧ gb.values = fb.values ∧ gb.controls = fb.controls ∧ gb.auxInt = fb.auxInt
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧
    ((DSE.sameV fv gv = true ∧ keptOK tabs f E fv = true) ∨
      (elimV fv gv = true ∧ ∃ n, fv.aux = some n ∧ n ∈ E))
  none : ∀ x, f.value? x = none → g.value? x = none
  sched : ∀ bid ∈ f.blocks, ∀ fb gb, f.block? bid = some fb → g.block? bid = some gb →
    ∀ oS, Sem.schedule f fb = some oS → ∃ oT, Sem.schedule g gb = some oT ∧
      oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g)

/-- **The checker is sound.** -/
theorem urel_sound {tabs : Tables} {f g : Func} (h : urel tabs f g = true) :
    URel tabs f g (names f g) := by
  unfold urel at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hlow⟩, hE⟩, hblk⟩, hval⟩, hsch⟩ := h
  refine ⟨hcfg, hown, hsz, hlow, fun n hn => ?_, fun n hn => ?_, fun bid hb fb hfb => ?_,
    fun x fv hfv => ?_, fun x hx => ?_, fun bid hb fb gb hfb hgb oS hoS => ?_⟩
  · have := hE n hn
    unfold DAE.unforgeable at this
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.1
  · have := hE n hn
    unfold DAE.unforgeable at this
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.2
  · have := hblk bid hb
    unfold blockOK at this
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      obtain ⟨⟨⟨hk, hv⟩, hc⟩, ha⟩ := this
      exact ⟨gb, rfl, hk, hv, hc, ha⟩
  · have hv := hval x (DSE.lt_of_value? hfv)
    unfold valueOK at hv
    rw [hfv] at hv
    cases hgv : g.value? x with
    | none => rw [hgv] at hv; cases hv
    | some gv =>
      rw [hgv] at hv
      simp only [Bool.or_eq_true, Bool.and_eq_true, Option.any_eq_true,
        List.contains_iff_mem] at hv
      refine ⟨gv, rfl, ?_⟩
      rcases hv with ⟨hs, hk⟩ | ⟨he, n, hn, hnE⟩
      · exact .inl ⟨hs, hk⟩
      · exact .inr ⟨he, n, hn, hnE⟩
  · by_cases hlt : x < f.valueTab.size
    · have hv := hval x hlt
      unfold valueOK at hv
      rw [hx] at hv
      simpa using hv
    · have : g.valueTab.size ≤ x := by rw [hsz]; exact Nat.le_of_not_lt hlt
      unfold Func.value?
      rw [Array.getElem?_eq_none this]; rfl
  · have := hsch bid hb
    unfold DSE.schedOK at this
    rw [hfb, hgb] at this
    simp only [hoS] at this
    cases hoT : Sem.schedule g gb with
    | none => rw [hoT] at this; cases this
    | some oT =>
      rw [hoT] at this
      simp only [beq_iff_eq] at this
      exact ⟨oT, rfl, this⟩

/-! ## Reading the conditions -/

theorem elimV_spec {fv gv : Value} (h : elimV fv gv = true) :
    fv.op ∈ elimOps ∧ gv.op = .Copy ∧ gv.aux = none ∧ gv.auxInt = 0 ∧ gv.id = fv.id ∧
      gv.type = fv.type ∧ gv.block = fv.block ∧ ∃ m, fv.args.back? = some m ∧ gv.args = #[m] := by
  unfold elimV at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hop, hc⟩, hax⟩, hai⟩, hid⟩, hty⟩, hbl⟩, hargs⟩ := h
  refine ⟨hop, hc, hax, hai, hid, hty, hbl, ?_⟩
  revert hargs
  cases fv.args.back? with
  | none => intro h; cases h
  | some m => intro h; exact ⟨m, rfl, by simpa using h⟩

theorem elimV_ne_same {fv gv : Value} (he : elimV fv gv = true) (hs : DSE.sameV fv gv = true) :
    False := by
  obtain ⟨hop, hc, -⟩ := elimV_spec he
  have := (DSE.sameV_spec hs).2.1
  rw [hc] at this
  rw [← this] at hop
  simp [elimOps] at hop

theorem keptOK_spec {tabs : Tables} {f : Func} {E : List AuxRef} {fv : Value}
    (h : keptOK tabs f E fv = true) :
    (∀ n, fv.aux = some n → n ∉ E) ∧
    (fv.op = .Phi ∨ (∀ a ∈ fv.args, plainArg tabs f a = true) ∨
      ((∀ a ∈ fv.args.pop, plainArg tabs f a = true) ∧
        (fv.op ∈ DAE.memOps ∨ (fv.op ∈ armMemOps ∧ memLast tabs f fv = true)))) := by
  unfold keptOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Array.all_eq_true',
    List.contains_iff_mem, Bool.not_eq_true', Option.any_eq_false_iff_get] at h
  obtain ⟨hn, h1⟩ := h
  refine ⟨fun n hax hnE => ?_, ?_⟩
  · have := hn (by rw [hax]; rfl)
    simp only [hax, Option.get_some, List.contains_iff_mem] at this
    exact absurd hnE (by simpa using this)
  · rcases h1 with (h | h) | ⟨h, h'⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨h, h'⟩)

theorem memLast_spec {tabs : Tables} {f : Func} {fv : Value} (h : memLast tabs f fv = true) :
    ∃ m mv, fv.args.back? = some m ∧ f.value? m = some mv ∧ shapeOf tabs f mv.type = .mem := by
  unfold memLast at h
  cases hb : fv.args.back? with
  | none => rw [hb] at h; cases h
  | some m =>
    rw [hb] at h
    simp only [Option.bind_some] at h
    cases hm : f.value? m with
    | none => rw [hm] at h; cases h
    | some mv =>
      rw [hm] at h
      simp only at h
      refine ⟨m, mv, rfl, hm, ?_⟩
      revert h
      cases shapeOf tabs f mv.type <;> simp

end GoFV.Proof.UnreadL
