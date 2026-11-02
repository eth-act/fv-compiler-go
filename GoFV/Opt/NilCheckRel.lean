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
  into an allocation (`safePtr`: `Addr`, `LocalAddr`, a nil check, `GetG`, the `StringPtr` of a
  non-empty string constant, or `OffPtr`/`AddPtr`/`PtrIndex`/`Copy` of such a pointer or a
  `StructSelect` of a `StructMake`'s pointer field that is one, all pointer-typed);
* an `IsNonNil p` may become `ConstBool [1]` when a nil check of `p` justifies it or `p` holds a
  non-nil pointer whenever it is evaluated (`nnSeed`: an `Addr` of a symbol or a `LocalAddr` with
  a name, word-typed; Go's `nonNilValues`);

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

/-- The malloc-family runtime entry points (`isMalloc`, `rewrite.go`): `runtime.newobject` and the
size-specialised allocators. Their contracts return a non-nil pointer under the checked rewrite
passes' precondition `Sem.Env.AllocNonNil`. -/
def mallocName (name : String) : Bool :=
  name == "runtime.newobject" || name.startsWith "runtime.mallocgcTinySC" ||
    name.startsWith "runtime.mallocgcSmallNoScanSC" ||
    name.startsWith "runtime.mallocgcSmallScanNoHeaderSC"

/-- `c` is a `StaticLECall` of a malloc-family entry point whose first result is pointer-shaped,
in the call's type and in its ABI's first result. -/
def mallocCall (tabs : Tables) (f : Func) (c : ID) : Bool :=
  match f.value? c with
  | some cv =>
    cv.op == .StaticLECall && ((cv.aux.bind tabs.callee?).map mallocName).getD false &&
      (match tabs.ty cv.type with
       | .tuple (.ptr _ :: _) => true
       | _ => false) &&
      match (((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out) with
      | [] => true
      | p :: _ => ptrShaped tabs p.type
  | none => false

/-- `n` names the generic dictionary parameter `.dict` (`isDictArgSym`). -/
def dictName (tabs : Tables) (n : AuxRef) : Bool :=
  match tabs.aux? n with
  | some { kind := .name sym .., .. } => sym.bytes == ".dict".toUTF8
  | _ => false

/-- `f`'s input parameters (`Sem.Ctx.make`'s `params` are their names). -/
def inParams (tabs : Tables) (f : Func) : Array ABIParam := (Sem.abiParams tabs f).filter (!·.out)

/-- The indices of `f`'s dictionary parameters among its inputs: the checked rewrite passes
assume that these arguments are non-nil pointers (`Sem.DictArgs`). -/
def dictParams (tabs : Tables) (f : Func) : List Nat :=
  let ps := inParams tabs f
  (List.range ps.size).filter fun i => ((ps[i]?.bind (·.name)).map (dictName tabs)).getD false

/-- `Arg {n}` reads input parameter `n` (`Sem.argVal`), a dictionary parameter of pointer
shape. -/
def dictArg (tabs : Tables) (f : Func) (n : AuxRef) : Bool :=
  let ps := inParams tabs f
  match (ps.map (·.name)).findIdx? (· == some n) with
  | some i => dictName tabs n && match ps[i]? with
    | some p => ptrShaped tabs p.type
    | none => false
  | none => false

/-- A non-empty string constant: `ConstString` whose aux is a string of non-zero length (its data
pointer is the start of a global, `Sem.frameVal`). -/
def nonEmptyStr (tabs : Tables) (f : Func) (a : ID) : Bool :=
  match f.value? a with
  | some av =>
    av.op == .ConstString &&
      match av.aux.bind tabs.aux? with
      | some { kind := .str s _, .. } => s.size != 0
      | _ => false
  | none => false

/-- Field `i` of the aggregate shape of type `t` is pointer-shaped. -/
def ptrField (tabs : Tables) (t : TypeRef) (i : Nat) : Bool :=
  match tabs.ty t with
  | .agg fs _ =>
    match fs[i]? with
    | some (_, .ptr _) => true
    | _ => false
  | _ => false

/-- The type of `t` has word shape: a pointer or a 64-bit integer (`uintptr`). -/
def wordShaped (tabs : Tables) (t : TypeRef) : Bool :=
  match tabs.ty t with
  | .ptr _ | .int .w64 => true
  | _ => false

/-- `x` is word-typed and holds a non-nil pointer whenever it is evaluated (`Sem.frameVal`,
never `poison`; at an integer shape the pointer's word): an `Addr` of a symbol or a `LocalAddr`
with a name. -/
def nnSeed (tabs : Tables) (f : Func) (x : ID) : Bool :=
  match f.value? x with
  | some v =>
    wordShaped tabs v.type &&
      match v.op with
      | .LocalAddr => v.aux.isSome
      | .Addr =>
        match v.aux.bind tabs.aux? with
        | some { kind := .sym .., .. } => true
        | _ => false
      | _ => false
  | none => false

/-- `x` is pointer-typed and points into an allocation whenever it is defined: an `Addr` or
`LocalAddr` with a name, a nil check, `GetG` (the goroutine's `g`, an allocation of the
environment, `docs/plans/semantics.md` §5), the `StringPtr` of a non-empty string constant
(`nonEmptyStr`), an `OffPtr`/`AddPtr`/`PtrIndex`/`Copy` of such a value, a `Convert` of one or
of an `nnSeed` (at a pointer shape the identity on the word, `generic.rules:1376`; a fixed load
can give the `Addr` an integer type), or a `StructSelect [i]`
of a `StructMake` whose field `i` is pointer-shaped (`ptrField`) and such a value. With `xt` (the
checked rewrite passes, under `Sem.Env.AllocNonNil` and `Sem.DictArgs`) also the first result of
a malloc-family call (`mallocCall`) and a dictionary parameter (`dictArg`). -/
def safePtr (xt : Bool) (tabs : Tables) (f : Func) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, x =>
    match f.value? x with
    | none => false
    | some v =>
      ptrShaped tabs v.type &&
      match v.op with
      | .Addr | .LocalAddr => v.aux.isSome
      | .NilCheck | .GetG => true
      | .OffPtr | .AddPtr | .PtrIndex | .Copy =>
        match v.args[0]? with
        | some a => safePtr xt tabs f n a
        | none => false
      | .Convert =>
        match v.args[0]? with
        | some a => safePtr xt tabs f n a || nnSeed tabs f a
        | none => false
      | .StringPtr =>
        match v.args[0]? with
        | some a => nonEmptyStr tabs f a
        | none => false
      | .StructSelect =>
        match v.args[0]? with
        | some a =>
          match f.value? a with
          | some sm =>
            sm.op == .StructMake && decide (0 ≤ v.auxInt.toInt) &&
              ptrField tabs sm.type v.auxInt.toInt.toNat &&
              match sm.args[v.auxInt.toInt.toNat]? with
              | some b => safePtr xt tabs f n b
              | none => false
          | none => false
        | none => false
      | .SelectN =>
        xt && v.auxInt == 0 &&
          match v.args[0]? with
          | some c => mallocCall tabs f c
          | none => false
      | .Arg =>
        xt && v.auxInt == 0 &&
          match v.aux with
          | some n => dictArg tabs f n
          | none => false
      | _ => false

/-- `o` lists `a` before `b`. -/
def listedBefore (o : Array ID) (a b : ID) : Bool :=
  match o.findIdx? (· == a), o.findIdx? (· == b) with
  | some i, some j => decide (i < j)
  | _, _ => false

/-- `ptr` is non-nil at value `x` of block `bx`: `nc` is a nil check of `ptr` (of type `ty`)
listed in a strict dominator of `bx` or before `x` in `bx`'s schedule; or (`seed`) `nc = ptr`
and `safePtr xt`. -/
def justified (xt : Bool) (tabs : Tables) (c : DomCert.Cert) (f : Func) (bx x ptr nc : ID)
    (ty : TypeRef) (seed : Bool) : Bool :=
  if nc == ptr then seed && safePtr xt tabs f f.valueTab.size ptr
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

/-- `x` is unchanged, a justified removed nil check, or a justified constant `IsNonNil` (by a nil
check or `nnSeed`). -/
def valueOK (xt : Bool) (tabs : Tables) (c : DomCert.Cert) (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | none, none => true
  | some fv, some gv =>
    gv.id == fv.id && gv.block == fv.block && gv.type == fv.type &&
    ((gv.op == fv.op && gv.args == fv.args && gv.aux == fv.aux && gv.auxInt == fv.auxInt) ||
     (fv.op == .NilCheck && gv.op == .Copy && gv.args.size == 1 &&
       match fv.args[0]?, gv.args[0]? with
       | some p, some nc => justified xt tabs c f fv.block x p nc fv.type true || after f g fv x nc
       | _, _ => false) ||
     (fv.op == .IsNonNil && gv.op == .ConstBool && gv.auxInt == 1 && gv.args.size == 0 &&
       fv.args.size == 1 &&
       match fv.args[0]? with
       | some p => nnSeed tabs f p || (List.range f.valueTab.size).any fun nc =>
           nc != p && justified xt tabs c f fv.block x p nc ((f.getV nc).type) false
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

/-- **The checker** (`xt`: with the seeds of `safePtr xt`). -/
def nrel (xt : Bool) (tabs : Tables) (f g : Func) : Bool :=
  let c := DomCert.make f
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    g.valueTab.size == f.valueTab.size &&
    f.blocks.all (blockOK f g) &&
    (List.range f.valueTab.size).all (valueOK xt tabs c f g) &&
    f.blocks.all (schedOK f g)

end NilCheck

/-- `nilcheckelim`'s output on `f` passes the checker. -/
def nilFrag (penv : PassEnv) (f : SSA.Func) : Bool :=
  match nilcheckelim penv f with
  | .ok g => NilCheck.nrel false penv.tables f g
  | .error _ => false

end GoFV.Opt
