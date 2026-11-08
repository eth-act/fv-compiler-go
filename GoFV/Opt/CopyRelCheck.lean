import GoFV.SSA.DomCert
import GoFV.Proof.Pass.CopyFrag

variable [GoFV.SSA.Sem.Addrs]

/-!
# `Phi`s turned copies: the checker of copyelim's relation

`copyOK tabs k g`: `g` has `k`'s control-flow graph, blocks and values, except that a `Phi` of
`k` may be `Copy w` in `g` where each of its arguments is `w` or a copy of `w` in `g`; copies of
`g` retype like their argument, and no value of `k` has a zero-size aggregate type
(`CopyElim.CopyRel` and `CopyElim.EmptyFrag`, `GoFV.Proof.CopyRelCheck.copyOK_spec`). Used by
sccp (`removeEdge`'s `phielimValue`) and by the rewrite validator's phi layer
(`applyRewrite`'s `phielimValue`, `RewriteCheck.phiPre`).
-/

namespace GoFV.Opt.CopyCheck

open GoFV.SSA

/-- The argument `a` of a `Phi` that became `Copy w` in `g`: `w`, or a copy of `w` in `g`. -/
def copyArg (g : Func) (w a : ID) : Bool :=
  a == w || (g.value? a).any fun u => u.op == .Copy && u.args == #[w]

/-- `g`'s value `x` (listed in block `kb` of `k`) is `k`'s or a `Phi` of `k` turned copy,
copies of `g` retype like their argument (the two word shapes alike, #290: a `Phi <uintptr>` of
`Addr`s turned copy, issue #17), and `k`'s value has no zero-size aggregate type. -/
def copyValueOK (tabs : Tables) (k g : Func) (x : ID) : Bool :=
  (match k.value? x, g.value? x with
    | some kv, some gv =>
      gv.block == kv.block && gv.type == kv.type &&
      (match zeroSizeAggregate tabs kv.type with | .ok true => false | _ => true) &&
      ((gv.op == kv.op && gv.aux == kv.aux && gv.auxInt == kv.auxInt && gv.args == kv.args) ||
        (kv.op == .Phi && gv.op == .Copy && gv.args == #[gv.args[0]!] &&
          kv.args.all (copyArg g gv.args[0]!)))
    | some _, none => false
    | none, _ => true) &&
  (g.value? x).all fun gv => gv.op != .Copy || gv.args.size != 1 ||
    (g.value? gv.args[0]!).any fun wv =>
      GoFV.Proof.CopyElim.retypeEqB (tabs.ty wv.type) (tabs.ty gv.type)

/-- **`g` is `k` with some `Phi`s turned copies** (`CopyElim.CopyRel tabs k g` and
`CopyElim.EmptyFrag tabs k`). -/
def copyOK (tabs : Tables) (k g : Func) : Bool :=
  DomCert.cfgView g == DomCert.cfgView k && g.ownAux == k.ownAux &&
  g.valueTab.size == k.valueTab.size &&
  k.blocks.all fun b =>
    match k.block? b, g.block? b with
    | some kb, some gb =>
      gb.kind == kb.kind && gb.values == kb.values && gb.controls == kb.controls &&
      kb.values.all (copyValueOK tabs k g)
    | some _, none => false
    | none, _ => true

end GoFV.Opt.CopyCheck
