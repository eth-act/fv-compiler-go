import GoFV.Opt.RewriteCheck

-- DEV ONLY: moved into GoFV/Opt/RewriteCheck.lean before the PR.

namespace GoFV.Opt.RewriteCheck

open GoFV.SSA GoFV.Rules

/-- The `Phi` `v` of `f` (of a `bool` shape, in a block other than the entry) is `Not p` in `g`
(same type and block): `p` is not a value of `f`, and in `g` a `Phi` of `v`'s type listed in
`v`'s block whose argument `j` is the argument `x_j` of `v`'s argument `j`, a `Not`, both of a
`bool` shape. -/
def pnOK (tabs : Tables) (f g : Func) (v : ID) : Bool :=
  match f.value? v, g.value? v with
  | some u, some w =>
    match w.args[0]? with
    | some p =>
      u.op == .Phi && w.op == .Not && w.args.size == 1 && w.id == v && w.block == u.block &&
        w.type == u.type && tabs.ty u.type matches .bool && u.block != f.entry &&
        (f.value? p).isNone && (g.block? u.block).any (·.values.contains p) &&
        (g.value? p).any fun pv =>
          pv.op == .Phi && pv.id == p && pv.block == u.block && pv.type == u.type &&
            pv.args.size == u.args.size &&
            (pv.args.toList.zip u.args.toList).all fun (c, a) =>
              (f.value? a).any fun av =>
                av.op == .Not && av.args.size == 1 && av.args[0]? == some c &&
                  tabs.ty av.type matches .bool &&
                  (f.value? c).any fun cv => tabs.ty cv.type matches .bool
    | none => false
  | _, _ => false

/-- `z` is the fresh `Phi` of a `pnOK` value listed in `z`'s block of `g`. -/
def pnFresh (tabs : Tables) (f g : Func) (z : ID) : Bool :=
  match g.value? z with
  | some zv => (g.block? zv.block).any fun gb => gb.values.any fun v =>
      pnOK tabs f g v && (g.value? v).any (·.args[0]? == some z)
  | none => false

/-- **The `Phi`-of-`Not`s relation**: `g` is `f` with `Phi`s turned `Not`s of fresh `Phi`s
(`pnOK`): the same control-flow graph and own aux; every other value of `f` kept but for its use
count, every value `f` lacks such a fresh `Phi`; per block the same kind and controls, the
source's values in the same order with only fresh `Phi`s added, and the source's schedule the
target's without the turned `Phi`s. -/
def pnRel (tabs : Tables) (f g : Func) : Bool :=
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    decide (f.valueTab.size ≤ g.valueTab.size) &&
    (List.range g.valueTab.size).all (fun z => match f.value? z, g.value? z with
      | none, none => true
      | some fv, some gv => ssSame fv gv || pnOK tabs f g z
      | none, some _ => pnFresh tabs f g z
      | some _, none => false) &&
    f.blocks.all fun b => match f.block? b, g.block? b with
      | some fb, some gb =>
        gb.kind == fb.kind && gb.controls == fb.controls &&
          gb.values.toList.filter (fun z => (f.value? z).isSome) == fb.values.toList &&
          gb.values.all (fun z => (f.value? z).isSome || pnFresh tabs f g z) &&
          (match Sem.schedule f fb, Sem.schedule g gb with
            | some of, some og => og.toList.filter (fun z => !pnOK tabs f g z) == of.toList
            | _, _ => false)
      | _, _ => false

end GoFV.Opt.RewriteCheck
