import GoFV.Opt.NilCheck
import GoFV.SSA.DomCert
import GoFV.SSA.Sem.Run

/-!
# nilcheckelim's output relation (checker)

`NilCheck.nrel tabs f g`: `g` is `f` with the same control-flow graph, blocks (kinds, controls,
the same values possibly reordered, the `Phi`s in the same order) and values, except that

* a `NilCheck p mem` may become `Copy nc` when `p` is known to point into an allocation there
  (`justified`): `nc` is a nil check of `p` (with `p`'s check's type) in a strict dominator of
  the block or listed before it in the block's schedule, or `nc = p` and `p`'s op makes it point
  into an allocation (`safePtr`: `Addr`, `LocalAddr`, a nil check, `GetG`, or `OffPtr`/`AddPtr`
  of such a pointer, all pointer-typed);
* an `IsNonNil p` may become `ConstBool [1]` when a nil check of `p` justifies it;

and every block's schedule in `g` runs the roots of `f`'s, minus the removed checks, in the same
order. `nilFrag penv f`: the checker accepts `nilcheckelim`'s output. Go's remaining assumptions
(`OffPtr`/`AddPtr`/`Add`/`Sub`/`SlicePtr` of an unchecked pointer are non-nil,
`docs/plans/semantics.md` §10; phis of non-nil values; `If (IsNonNil p)` edges) are outside.
-/

namespace GoFV.Opt.NilCheck

open GoFV.SSA

/-- `x` is a root of `f`'s schedules (non-zero priority). -/
def root (f : Func) (x : ID) : Bool := ((f.value? x).map (Sem.prio ·.op)).getD 0 != 0

/-- The type of `t` has pointer shape. -/
def ptrShaped (tabs : Tables) (t : TypeRef) : Bool :=
  match tabs.ty t with
  | .ptr _ => true
  | _ => false

/-- `x` is pointer-typed and points into an allocation whenever it is defined: an `Addr` or
`LocalAddr` with a name, a nil check, `GetG` (the goroutine's `g`, an allocation of the
environment, `docs/plans/semantics.md` §5), or an `OffPtr`/`AddPtr` of such a value. -/
def safePtr (tabs : Tables) (f : Func) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, x =>
    match f.value? x with
    | none => false
    | some v =>
      ptrShaped tabs v.type &&
      match v.op with
      | .Addr | .LocalAddr => v.aux.isSome
      | .NilCheck | .GetG => true
      | .OffPtr | .AddPtr =>
        match v.args[0]? with
        | some a => safePtr tabs f n a
        | none => false
      | _ => false

/-- `o` lists `a` before `b`. -/
def listedBefore (o : Array ID) (a b : ID) : Bool :=
  match o.findIdx? (· == a), o.findIdx? (· == b) with
  | some i, some j => decide (i < j)
  | _, _ => false

/-- `ptr` is non-nil at value `x` of block `bx`: `nc` is a nil check of `ptr` (of type `ty`)
listed in a strict dominator of `bx` or before `x` in `bx`'s schedule; or (`seed`) `nc = ptr`
and `safePtr`. -/
def justified (tabs : Tables) (c : DomCert.Cert) (f : Func) (bx x ptr nc : ID) (ty : TypeRef)
    (seed : Bool) : Bool :=
  if nc == ptr then seed && safePtr tabs f f.valueTab.size ptr
  else
    match f.value? nc, f.block? bx with
    | some n, some fb =>
      n.op == .NilCheck && n.args[0]? == some ptr && n.type == ty &&
      if n.block == bx then
        fb.values.contains nc &&
          match Sem.schedule f fb with
          | some o => listedBefore o nc x
          | none => false
      else
        c.anc n.block bx && f.blocks.contains n.block &&
          match f.block? n.block with
          | some nb => nb.values.contains nc
          | none => false
    | _, _ => false

/-- `nc`, the nil check `x` became a copy of, is listed right after `x` among the block's roots
in its schedule and checks the same pointer with the same memory: when `x` panics in the source,
`nc` panics alike in the target, and nothing runs in between. -/
def after (f g : Func) (fv : Value) (x nc : ID) : Bool :=
  match f.value? nc, f.block? fv.block, g.value? nc with
  | some n, some fb, some gn =>
    nc != x && n.op == .NilCheck && n.args == fv.args && n.type == fv.type &&
      n.block == fv.block && gn.op == .NilCheck && gn.args == n.args && fb.values.contains nc &&
      match Sem.schedule f fb with
      | some o =>
        match o.findIdx? (· == x), o.findIdx? (· == nc) with
        | some i, some j =>
          decide (i < j) && (List.range o.size).all fun k => !(decide (i < k) && decide (k < j)) ||
            !root f o[k]!
        | _, _ => false
      | none => false
  | _, _, _ => false

/-- `x` is unchanged, a justified removed nil check, or a justified constant `IsNonNil`. -/
def valueOK (tabs : Tables) (c : DomCert.Cert) (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | none, none => true
  | some fv, some gv =>
    gv.id == fv.id && gv.block == fv.block && gv.type == fv.type &&
    ((gv.op == fv.op && gv.args == fv.args && gv.aux == fv.aux && gv.auxInt == fv.auxInt) ||
     (fv.op == .NilCheck && gv.op == .Copy && gv.args.size == 1 &&
       match fv.args[0]?, gv.args[0]? with
       | some p, some nc => justified tabs c f fv.block x p nc fv.type true || after f g fv x nc
       | _, _ => false) ||
     (fv.op == .IsNonNil && gv.op == .ConstBool && gv.auxInt == 1 && gv.args.size == 0 &&
       fv.args.size == 1 &&
       match fv.args[0]? with
       | some p => (List.range f.valueTab.size).any fun nc =>
           nc != p && justified tabs c f fv.block x p nc ((f.getV nc).type) false
       | none => false))
  | _, _ => false

/-- `g`'s block has `f`'s kind, controls and values (reordered, the `Phi`s in order). -/
def blockOK (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.controls == fb.controls &&
      gb.values.toList.isPerm fb.values.toList &&
      gb.values.filter (fun z => (g.getV z).op == .Phi) ==
        fb.values.filter (fun z => (f.getV z).op == .Phi)
  | _, _ => false

/-- `g`'s schedule of the block runs `f`'s roots minus the removed checks in `f`'s order. -/
def schedOK (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    match Sem.schedule f fb with
    | none => true
    | some oS =>
      match Sem.schedule g gb with
      | some oT => oT.filter (root g) == oS.filter (root g)
      | none => false
  | _, _ => false

/-- **The checker.** -/
def nrel (tabs : Tables) (f g : Func) : Bool :=
  let c := DomCert.make f
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    g.valueTab.size == f.valueTab.size &&
    f.blocks.all (blockOK f g) &&
    (List.range f.valueTab.size).all (valueOK tabs c f g) &&
    f.blocks.all (schedOK f g)

end NilCheck

/-- `nilcheckelim`'s output on `f` passes the checker. -/
def nilFrag (penv : PassEnv) (f : SSA.Func) : Bool :=
  match nilcheckelim penv f with
  | .ok g => NilCheck.nrel penv.tables f g
  | .error _ => false

end GoFV.Opt
