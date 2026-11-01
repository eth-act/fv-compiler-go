import GoFV.Opt.RewriteCheck
import GoFV.Opt.SccpCheck

/-!
# decompose builtin: the phi eliminations of the dec-rule rewrite as a stage (issue #17)

The rewrite loop of decompose builtin turns a `Phi` whose arguments (other than itself) became
one value `w` into `Copy w` (`phielimValue`, logged as `RwEvent.phielim`), typically after the
dec rules made the arguments of a split phi copies of one component (`Phi (SliceLen a)
(SliceLen b)` with `a`, `b` slices of one length). The rewrite validator relates terms only and
rejects these events. They are taken out of the rewrite instead:

- `phStrip` replays the log without them: a phi it eliminated stays a `Phi` (with its arguments
  at that point), and a copy-argument replacement whose copy chain passes through such a phi
  stops at the phi (`phFirst`). The result `h` is the rewrite's output `g` with those phis and
  arguments (`phDef`; an eliminated phi that `g` dropped as dead is listed again, first in its
  block; use counts recounted, `recountUses`), and the stripped log `log'` is validated against
  `h` as before;
- `k` is `g` with the eliminated phis it dropped listed again as their copies. `phRelOK tabs h k`
  relates `h` and `k` by copyelim's static relation (`CopyElim.CopyRel`): the same blocks, every
  value of `h` kept but for arguments related by one copy of `k` (`phArg`), or a `Phi` of `h`
  that is `Copy w` in `k` with every argument `w` or a copy of `w` in `k`; no zero-size
  aggregate values (`CopyElim.EmptyFrag`). Then `k` refines `h` (`CopyElim.refines_of_rel`);
- `g` is `k` without those copies (`Sccp.deadOK k g`, `Dead.refines_of_deadRel`).
-/

namespace GoFV.Opt.DecPhiElim

open GoFV.SSA GoFV.Rules GoFV.Opt.RewriteCheck

/-- The first phi eliminated so far (`isP`) on the copy chain (in `M`) from `a` towards `src`,
`a` included; `none` if the chain reaches `src` or ends first. -/
def phFirst (M : Defs) (isP : ID → Bool) : Nat → ID → ID → Option ID
  | 0, _, _ => none
  | n + 1, a, src =>
    if isP a then some a
    else if a == src then none
    else match M.get? a with
      | some x => if x.op == .Copy && x.args.size == 1 then phFirst M isP n x.args[0]! src else none
      | none => none

/-- The state of `phStrip`: the definitions of the stripped replay, the eliminated phis with the
value each is a copy of in the rewrite, the values whose arguments the strip changed, and the
stripped log. -/
structure PhSt where
  M : Defs
  cp : Array (Option ID)
  mark : Array Bool
  log : Array RwEvent

@[inline] def PhSt.isP (s : PhSt) (x : ID) : Bool := (s.cp[x]?).join.isSome

/-- Replace argument `i` of `v` in `M`. -/
def setArg (M : Defs) (v : ID) (i : Nat) (a : ID) : Defs :=
  match M.get? v with
  | some x => M.put v { x with args := x.args.set! i a }
  | none => M

/-- One event of the stripped replay. -/
def phStep (s : PhSt) (ev : RwEvent) : PhSt :=
  match ev with
  | .rule _ _ _ defs =>
    { s with M := defs.foldl (fun M u => M.put u.id u) s.M, log := s.log.push ev }
  | .copyArg v i src =>
    if s.isP v then { s with cp := s.cp.set! v (some src) } else
    match s.M.get? v with
    | none => { s with log := s.log.push ev }
    | some x =>
      match x.args[i]? with
      | none => { s with log := s.log.push ev }
      | some a =>
        match phFirst s.M s.isP s.M.size a src with
        | none => { s with M := setArg s.M v i src, log := s.log.push ev }
        | some t =>
          if t == a then { s with mark := s.mark.set! v true }
          else { s with M := setArg s.M v i t, mark := s.mark.set! v true,
                        log := s.log.push (.copyArg v i t) }
  | .phielim v d => { s with cp := s.cp.set! v d.args[0]?, mark := s.mark.set! v true }
  | .control .. | .blockRule .. => { s with log := s.log.push ev }

/-- `f` with every listed value's use count recounted from the listed values' arguments and the
blocks' controls. -/
def recountUses (f : Func) : Func := Id.run do
  let mut uses : Array Nat := Array.replicate f.valueTab.size 0
  for b in f.blocks do
    let some bb := f.block? b | continue
    for vid in bb.values do
      let some v := f.value? vid | continue
      for a in v.args do
        uses := uses.modify a (· + 1)
    for c in bb.controls do
      uses := uses.modify c (· + 1)
  return { f with valueTab := f.valueTab.mapIdx fun i o => o.map fun v => { v with uses := uses[i]! } }

/-- The eliminated phis `g` dropped, listed again first in their blocks (`relist`). -/
def dropped (s : PhSt) (g : Func) : List (ID × ID) :=
  (List.range s.cp.size).filterMap fun x =>
    if s.isP x && (g.value? x).isNone then (s.M.get? x).map fun m => (x, m.block) else none

/-- `g` with the values `xs` (value, block) listed first in their blocks (and not free). -/
def relist (g : Func) (xs : List (ID × ID)) : Func :=
  xs.foldl (fun g (x, b) =>
    { g.modB b (fun bb => { bb with values := #[x] ++ bb.values }) with
      freeValues := g.freeValues.filter (· != x) }) g

/-- The definition of `x` in `h`: an eliminated phi is a `Phi` with its replayed arguments (on
`g`'s definition, or the replay's if `g` dropped it), another marked value has its replayed
arguments. -/
def phDef (s : PhSt) (g : Func) (x : ID) : Option Value :=
  if (s.mark[x]?).getD false then
    match s.M.get? x, g.value? x with
    | some m, some gv =>
      some (if s.isP x then { gv with op := .Phi, args := m.args } else { gv with args := m.args })
    | some m, none => if s.isP x then some m else none
    | none, gv => gv
  else g.value? x

/-- The definition of `x` in `k`: `g`'s, or for an eliminated phi `g` dropped, its copy. -/
def cpDef (s : PhSt) (g : Func) (x : ID) : Option Value :=
  match g.value? x, (s.cp[x]?).join, s.M.get? x with
  | none, some w, some m => some { m with op := .Copy, args := #[w], auxInt := 0, aux := none }
  | gv, _, _ => gv

/-- `g` with the definitions `d` and the dropped eliminated phis listed again, uses recounted. -/
def phFunc (s : PhSt) (g : Func) (d : PhSt → Func → ID → Option Value) : Func :=
  recountUses (relist { g with valueTab := (Array.range g.valueTab.size).map (d s g) } (dropped s g))

/-- The rewrite log `log` of `f` (output `g`) without its phi eliminations: `h`, `k` and the
stripped log, `none` if the log has none. -/
def phStrip (f g : Func) (log : Array RwEvent) : Option (Func × Func × Array RwEvent) :=
  if !log.any (fun | .phielim .. => true | _ => false) then none else
  let n := max f.valueTab.size g.valueTab.size
  let s := log.foldl phStep { M := f.valueTab, cp := Array.replicate n none,
                              mark := Array.replicate n false, log := #[] }
  some (phFunc s g phDef, phFunc s g cpDef, s.log)

/-! ## The relation to the output -/

/-- Argument `a` of `h` is `a'` in `g`: the same value, or `a` is `Copy a'` in `g`
(`CopyElim.ArgRel g a a'`). -/
def phArg (g : Func) (a a' : ID) : Bool :=
  a == a' || (g.value? a).any fun u => u.op == .Copy && u.args == #[a']

/-- Pairwise `phArg`, same length. -/
def phArgs (g : Func) : List ID → List ID → Bool
  | [], [] => true
  | a :: as, a' :: as' => phArg g a a' && phArgs g as as'
  | _, _ => false

/-- `g`'s value `x` (listed in a block of `h`) is `h`'s with arguments related (`phArgs`), or a
`Phi` of `h` turned `Copy w` with every argument `w` or a copy of `w` in `g`; copies of `g`
retype like their argument; `h`'s value has no zero-size aggregate type. -/
def phValueOK (tabs : Tables) (h g : Func) (x : ID) : Bool :=
  (match h.value? x, g.value? x with
    | some kv, some gv =>
      gv.block == kv.block && gv.type == kv.type &&
      (match GoFV.Opt.zeroSizeAggregate tabs kv.type with | .ok true => false | _ => true) &&
      ((gv.op == kv.op && gv.aux == kv.aux && gv.auxInt == kv.auxInt &&
          phArgs g kv.args.toList gv.args.toList) ||
        (kv.op == .Phi && gv.op == .Copy && gv.args == #[gv.args[0]!] &&
          kv.args.all fun a => phArg g a gv.args[0]!))
    | some _, none => false
    | none, _ => true) &&
  (g.value? x).all fun gv => gv.op != .Copy || gv.args.size != 1 ||
    (g.value? gv.args[0]!).any fun wv =>
      GoFV.Proof.CopyElim.retypeEqB (tabs.ty wv.type) (tabs.ty gv.type)

/-- **`g` is `h` with phis turned copies and arguments through them** (`CopyElim.CopyRel tabs h
g` and `CopyElim.EmptyFrag tabs h`). -/
def phRelOK (tabs : Tables) (h g : Func) : Bool :=
  DomCert.cfgView g == DomCert.cfgView h && g.ownAux == h.ownAux &&
  g.valueTab.size == h.valueTab.size &&
  h.blocks.all fun b =>
    match h.block? b, g.block? b with
    | some kb, some gb =>
      gb.kind == kb.kind && gb.values == kb.values &&
      phArgs g kb.controls.toList gb.controls.toList &&
      kb.values.all (phValueOK tabs h g)
    | some _, none => false
    | none, _ => true

end GoFV.Opt.DecPhiElim
