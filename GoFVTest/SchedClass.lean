import GoFV.Opt.ScheduleCheck

/-!
# Why `scheduleCheck` rejects a scheduling (`schedl-probe`, `gofv-ssa-opt --verified`)

`why`: the first failing condition of `scheduleCheck`; `pairClasses`: the classes of all the
pairs of failing values the target runs against `swapOK`; `schedClass`: a rejected scheduling's
class (its `pairClasses`, or `why` when the order is not what fails).
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ScheduleCheck

namespace GoFVTest.SchedClass

def clsName : Cls → String
  | .safe => "safe" | .load => "load" | .nil => "nil" | .other => "other"

def opName (tabs : Tables) (f : Func) (x : ID) : String :=
  match f.value? x with
  | some v => s!"{v.op.name}/{clsName (cls tabs v)}{if mayPanic tabs v then "" else "/nopanic"}"
  | none => "none"

/-- The first failing condition of `scheduleCheck tabs f g`. -/
def why (tabs : Tables) (f g : Func) : String := Id.run do
  if g.entry != f.entry then return "entry"
  if g.ownAux != f.ownAux then return "ownAux"
  if g.lowered != f.lowered then return "lowered"
  if g.valueTab.size != f.valueTab.size then return "valueTab size"
  if g.blockTab.size != f.blockTab.size then return "blockTab size"
  for id in List.range f.valueTab.size do
    if !valueOK f g id then
      match f.value? id, g.value? id with
      | some fv, some gv =>
        if gv.args != fv.args.map (rep f) then
          -- the first argument `g` does not bypass as `rep` does, and what `f` has there
          let d := match (List.range fv.args.size).find? (fun k =>
              gv.args[k]? != fv.args[k]?.map (rep f)) with
            | some k =>
              let a := fv.args[k]!
              let c := if isSPA f a then "SPanchored"
                else if isNC f a then (if isNC f (rep1 f a) then "chain" else "nil check")
                else "plain"
              s!" (arg {k}: {c})"
            | none => " (arity)"
          return s!"value args {fv.op.name}{d}"
        if !(fv.op.nilCheck || gv.type == fv.type) then return s!"value type {fv.op.name}"
        return s!"value other {fv.op.name}"
      | _, _ => return "value presence"
  for b in List.range f.blockTab.size do
    if !blockOK f g b then
      match f.block? b, g.block? b with
      | some fb, some gb =>
        if gb.controls != fb.controls.map (rep f) then return "block controls"
        if !gb.values.toList.isPerm (fb.values.toList.filter (!isSPA f ·)) then
          return "block values perm"
        return "block other"
      | _, _ => return "block presence"
  if !usesOK tabs f then
    let tys := (Ctx.makeL tabs f).tys
    for o in f.valueTab do
      if let some u := o then
        for k in List.range u.args.size do
          let a := u.args[k]!
          if !useOK tabs tys f (some u) k a then
            if isSPA f a then
              return s!"use of SPanchored by {u.op.name} (arg {k}, rep {opName tabs f (rep1 f a)})"
            -- the first step of the nil-check chain that fails `ncStep`
            let mut c := a
            for _ in List.range f.valueTab.size do
              if !ncStep tys f c then break
              c := rep1 f c
            let p := rep1 f c
            if p == c then return s!"use: nil check without pointer ({opName tabs f c})"
            if isSPA f p then return "use: nil check of an SPanchored"
            return s!"use: nil check type ({repr (tys[c]?.getD .other)} vs {repr (tys[p]?.getD .other)})"
    return "uses (control)"
  let cS := Ctx.makeL tabs f
  let sS := cS.sched
  let sT := (Ctx.makeSched tabs g).sched
  for b in List.range f.blockTab.size do
    if (f.block? b).isNone then continue
    match sS[b]?.join, sT[b]?.join with
    | some oS, some oT =>
      if let some gb := g.block? b then
        if oT.toList != gb.values.toList.filter (!isPhi g ·) then return "target order: not the block's non-Phis"
        if !topoB g oT.toList then return "target order: not topological"
      else return "block presence (orders)"
      if !orderOK tabs cS.params cS.tys f f.valueTab.size oS oT then
        let pS := srcPos f.valueTab.size oS.toList
        let ns := oT.filter (mayFail tabs f)
        for l in List.range ns.size do
          for k in List.range l do
            let x := ns[l]!
            let y := ns[k]!
            if pS[x]! < pS[y]! && !swapOK tabs cS.params cS.tys f pS x y then
              let mem := match f.value? x, f.value? y with
                | some vx, some vy => s!"{sameMem f pS vx vy}, same ptr {vx.args[0]? == vy.args[0]?}, y ptr {(vy.args[0]?.bind f.value?).map (fun (u : Value) => u.op.name)} x base {(vx.args[0]?.bind f.value?).map (fun (u : Value) => u.op.name)}"
                | _, _ => "?"
              -- a nil check of a parameter piece: where the piece is, and whether it is `argPtr`
              let ap := match f.value? y with
                | some vy => match vy.args[0]? with
                  | some p =>
                    if ((f.value? p).map fun (u : Value) => u.op == Op.ArgIntReg).getD false then
                      let pos := if pS[p]! == 0 then "outside the block"
                        else if pS[p]! < pS[x]! then "before x" else "after x"
                      s!"; y's ArgIntReg {pos}, argPtr {argPtr tabs cS.params cS.tys f p}"
                    else ""
                  | none => ""
                | none => ""
              return s!"order: src {opName tabs f x} before {opName tabs f y} (same mem {mem}){ap}"
        return "order ?"
    | none, _ => return "no runL order"
    | _, none => return "no runSched order"
  return "accepted"

/-- The class of a pair the target swaps against `swapOK` (`x` first in the source; `pS`: the
source positions). -/
def pairCls (tabs : Tables) (params : Array (Option AuxRef)) (tys : Array Ty) (f : Func)
    (pS : Array Nat) (x y : ID) : String :=
  match f.value? x, f.value? y with
  | some vx, some vy =>
    let cx := cls tabs vx
    let cy := cls tabs vy
    if !(cx == .load || cx == .nil) then s!"x {vx.op.name}/{clsName cx}, y {vy.op.name}/{clsName cy}"
    else if !sameMem f pS vx vy then
      s!"different memory: x {vx.op.name}, y {vy.op.name}"
    else if cy != .nil then s!"x {vx.op.name}, y {vy.op.name}/{clsName cy}"
    else match vy.args[0]? with
      | some p =>
        let pos := if pS[p]! == 0 then "outside the block"
          else if pS[p]! < pS[x]! then "before x" else "after x"
        if vx.args[0]? == some p then s!"nil check of x's base, x {vx.op.name}"
        else if argPtr tabs params tys f p then s!"nil check of an argPtr piece {pos}"
        else
          let sh := if ptrShape (tys[p]?.getD .other) then "ptr" else "non-ptr"
          s!"nil check of another {sh} value {pos}"
      | none => "nil check without args"
  | _, _ => "missing value"

/-- The pairs of values that may fail and that the target runs against the source order, per
block: the source positions `pS`, then `(x, y)` with `x` first in the source. -/
def swapped (tabs : Tables) (f g : Func) : Array (Array Nat × ID × ID) := Id.run do
  let cS := Ctx.makeL tabs f
  let sS := cS.sched
  let sT := (Ctx.makeSched tabs g).sched
  let mut out := #[]
  for b in List.range f.blockTab.size do
    match sS[b]?.join, sT[b]?.join with
    | some oS, some oT =>
      let pS := srcPos f.valueTab.size oS.toList
      let ns := oT.filter (mayFail tabs f)
      for l in List.range ns.size do
        for k in List.range l do
          let x := ns[l]!
          let y := ns[k]!
          if pS[x]! < pS[y]! then out := out.push (pS, x, y)
    | _, _ => pure ()
  return out

/-- The sorted classes of all pairs the target swaps against `swapOK` (`[]`: none, or no order). -/
def pairClasses (tabs : Tables) (f g : Func) : List String := Id.run do
  let cS := Ctx.makeL tabs f
  let mut out : List String := []
  for (pS, x, y) in swapped tabs f g do
    if !swapOK tabs cS.params cS.tys f pS x y then
      let c := pairCls tabs cS.params cS.tys f pS x y
      if !out.contains c then out := c :: out
  return (out.toArray.qsort (· < ·)).toList

/-- Some pair the target swaps passes `swapOK` only through its `NilPtrsOK` case (`nilPtrSwap`):
an accepted scheduling relies on `GoFV.Proof.NilPtrsOK`. -/
def relyNilPtrs (tabs : Tables) (f g : Func) : Bool :=
  let cS := Ctx.makeL tabs f
  (swapped tabs f g).any fun (pS, x, y) =>
    !swapOKB tabs cS.params cS.tys f pS x y && nilPtrSwap tabs cS.tys f pS x y

/-- The source positions `pS` with every `argPtr` piece moved after the block: `swapOKB`'s
`argPtr` case never holds with them, its other cases as with `pS`. -/
def noArgPtrPos (tabs : Tables) (params : Array (Option AuxRef)) (tys : Array Ty) (f : Func)
    (pS : Array Nat) : Array Nat :=
  pS.mapIdx fun p k => if argPtr tabs params tys f p then pS.size + 1 else k

/-- Some pair the target swaps needs `swapOKB`'s `argPtr` case: it passes `swapOKB` only with
the `argPtr` pieces at their source positions (`noArgPtrPos`). -/
def relyArgPtrs (tabs : Tables) (f g : Func) : Bool :=
  let cS := Ctx.makeL tabs f
  (swapped tabs f g).any fun (pS, x, y) =>
    swapOKB tabs cS.params cS.tys f pS x y &&
      !swapOKB tabs cS.params cS.tys f (noArgPtrPos tabs cS.params cS.tys f pS) x y

/-- Some pair the target swaps passes `swapOK` only through a memory of an `LDAR*` (`sameMem`'s
`ldReach` step): it fails with the `Select1`s of `LDAR*`s not listed in the block. -/
def relyLdMem (tabs : Tables) (f g : Func) : Bool :=
  let cS := Ctx.makeL tabs f
  let sel1Ldar (z : ID) : Bool := match f.value? z with
    | some vz => vz.op == .Select1 &&
        ((vz.args[0]?.bind f.value?).map (ldarOp ·.op)).getD false
    | none => false
  (swapped tabs f g).any fun (pS, x, y) =>
    swapOK tabs cS.params cS.tys f pS x y &&
      !swapOK tabs cS.params cS.tys f (pS.mapIdx fun z k => if sel1Ldar z then 0 else k) x y

/-- The class of a scheduling `scheduleCheck` rejects: the classes of its pairs against
`swapOK` (`pairClasses`) when the order fails, else the first failing condition (`why`). -/
def schedClass (tabs : Tables) (f g : Func) : String :=
  let w := why tabs f g
  if w.startsWith "order" then " + ".intercalate (pairClasses tabs f g) else w

end GoFVTest.SchedClass
