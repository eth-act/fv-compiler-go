/-!
# Live intervals of stack-slot merge candidates

Port of `cmd/compile/internal/liveness/intervals.go` (go1.27.3, lines 58–384): `Interval`
(`[st,en)`), `Intervals` (sorted, disjoint), the backwards `IntervalsBuilder` (`Live`, `Kill`,
`Finish` with `check`), and the pair walk (`pairVisitor`) behind `Overlaps` and `Merge`.
`MergeLocals` (`GoFV.Gen.MergeLocals`) is the only client.

`Live` and `Kill` return Go's `error` as `Except String Unit` **without** changing the builder on
error, exactly as Go: the caller (`computeIntervals`) ignores those errors, so a rejected call is
a no-op.
-/

namespace GoFV.Gen

/-- `liveness.Interval`: the range `[st,en)`. -/
structure Interval where
  st : Int
  en : Int
  deriving DecidableEq, Inhabited, Repr

namespace Interval

/-- `Interval.String`. -/
def str (i : Interval) : String := s!"[{i.st},{i.en})"

/-- `Interval.Overlaps`: `imin(en) - imax(st) > 0`. -/
def overlaps (i i2 : Interval) : Bool := (min i.en i2.en - max i.st i2.st) > 0

/-- `Interval.adjacent`. -/
def adjacent (i1 i2 : Interval) : Bool := i1.en == i2.st || i2.en == i1.st

/-- `(*Interval).MergeInto`: the merged interval, or Go's error (then `i1` is unchanged). -/
def mergeInto (i1 i2 : Interval) : Except String Interval :=
  if !i1.overlaps i2 && !i1.adjacent i2 then
    throw "merge method invoked on non-overlapping/non-adjacent"
  else pure { st := min i1.st i2.st, en := max i1.en i2.en }

end Interval

/-- `liveness.Intervals`. -/
abbrev Intervals := Array Interval

/-- `liveness.IntervalsBuilder`: the intervals in reverse order and `lidx` (index of the last
instruction visited plus one; `last() == -1` means no lifetime is open). -/
structure IntervalsBuilder where
  s : Array Interval := #[]
  lidx : Int := 0
  deriving Inhabited

namespace IntervalsBuilder

def last (c : IntervalsBuilder) : Int := c.lidx - 1

def setLast (c : IntervalsBuilder) (x : Int) : IntervalsBuilder := { c with lidx := x + 1 }

/-- Replaces the start of the open (last) interval. -/
private def setLastSt (c : IntervalsBuilder) (st : Int) : IntervalsBuilder :=
  match c.s.back? with
  | some i => { c with s := c.s.pop.push { i with st } }
  | none => c  -- unreachable: `last() != -1` implies an open interval

/-- `(*IntervalsBuilder).Live`: the new builder, or Go's error (builder unchanged). -/
def live (c : IntervalsBuilder) (pos : Int) : Except String IntervalsBuilder :=
  if pos < 0 then throw "bad pos, negative"
  else if c.last == -1 then
    pure { (c.setLast pos) with s := c.s.push { st := pos, en := pos + 1 } }
  else if pos >= c.last then throw "pos not decreasing"
  else pure ((c.setLastSt pos).setLast pos)

/-- `(*IntervalsBuilder).Kill`. -/
def kill (c : IntervalsBuilder) (pos : Int) : Except String IntervalsBuilder :=
  if pos < 0 then throw "bad pos, negative"
  else if c.last == -1 then pure c
  else if pos >= c.last then throw "pos not decreasing"
  else pure ((c.setLastSt (pos + 1)).setLast (-1))

/-- `Live` with the error ignored (`computeIntervals` drops it). -/
def live! (c : IntervalsBuilder) (pos : Int) : IntervalsBuilder :=
  match c.live pos with | .ok c' => c' | .error _ => c

/-- `Kill` with the error ignored. -/
def kill! (c : IntervalsBuilder) (pos : Int) : IntervalsBuilder :=
  match c.kill pos with | .ok c' => c' | .error _ => c

end IntervalsBuilder

namespace Intervals

/-- `check(is)`. -/
def check (is : Intervals) : Except String Unit := do
  for h : i in [0:is.size] do
    let st := is[i].st
    let en := is[i].en
    if en <= st then throw s!"bad range elem {st}:{en}, en<=st"
    if i == 0 then continue
    let pst := is[i-1]!.st
    let pen := is[i-1]!.en
    if pst >= st then
      throw s!"range start not ordered {st}:{en} less than prev {pst}:{pen}"
    if pen > st then
      throw s!"bad range elem {st}:{en} overlaps prev {pst}:{pen}"

/-- `(*Intervals).String`. -/
def str (is : Intervals) : String := " ".intercalate (is.toList.map Interval.str)

end Intervals

/-- `(*IntervalsBuilder).Finish`: reverse, then `check`. -/
def IntervalsBuilder.finish (c : IntervalsBuilder) : Except String Intervals := do
  let r := c.s.reverse
  Intervals.check r
  return r

/-- `intWithIdx`: an interval and its side (0 or 1) of the pair; `pairIndex = -1` ends the walk. -/
structure IntWithIdx where
  i : Interval := { st := 0, en := 0 }
  pairIndex : Int := 0
  deriving Inhabited

/-- `pairVisitor`. -/
structure PairVisitor where
  cur : IntWithIdx := {}
  i1pos : Nat := 0
  i2pos : Nat := 0
  i1 : Intervals := #[]
  i2 : Intervals := #[]

namespace PairVisitor

/-- `(*pairVisitor).sel`. -/
def sel (pv : PairVisitor) : IntWithIdx :=
  let c1 : IntWithIdx := match pv.i1[pv.i1pos]? with
    | some i => { i, pairIndex := 0 }
    | none => { pairIndex := -1 }
  let c2 : IntWithIdx := match pv.i2[pv.i2pos]? with
    | some i => { i, pairIndex := 1 }
    | none => { pairIndex := -1 }
  if c1.pairIndex == -1 then c2
  else if c2.pairIndex == -1 then c1
  else if c1.i.st <= c2.i.st then c1
  else c2

/-- `(*pairVisitor).init`. -/
def init (i1 i2 : Intervals) : PairVisitor × IntWithIdx :=
  let pv : PairVisitor := { i1, i2 }
  let c := pv.sel
  ({ pv with cur := c }, c)

/-- `(*pairVisitor).nxt`. -/
def nxt (pv : PairVisitor) : PairVisitor × IntWithIdx :=
  let pv := if pv.cur.pairIndex == 0 then { pv with i1pos := pv.i1pos + 1 }
    else { pv with i2pos := pv.i2pos + 1 }
  let c := pv.sel
  ({ pv with cur := c }, c)

end PairVisitor

namespace Intervals

/-- `Intervals.Overlaps`. -/
def overlaps (is is2 : Intervals) : Bool := Id.run do
  if is.size == 0 || is2.size == 0 then return false
  if is[is.size - 1]!.en <= is2[0]!.st || is[0]!.st >= is2[is2.size - 1]!.en then return false
  let (pv0, first0) := PairVisitor.init is is2
  let mut pv := pv0
  let mut first := first0
  -- each step consumes one of the `is.size + is2.size` intervals
  for _ in [0:is.size + is2.size + 1] do
    let (pv', second) := pv.nxt
    pv := pv'
    if second.pairIndex == -1 then break
    if first.pairIndex == second.pairIndex then
      first := second
      continue
    if first.i.overlaps second.i then return true
    first := second
  return false

/-- `Intervals.Merge`. -/
def merge (is is2 : Intervals) : Intervals := Id.run do
  if is.size == 0 then return is2
  if is2.size == 0 then return is
  let mut ret : Intervals := #[]
  let (pv0, cur0) := PairVisitor.init is is2
  let mut pv := pv0
  let mut cur := cur0
  for _ in [0:is.size + is2.size + 1] do
    let (pv', second) := pv.nxt
    pv := pv'
    if second.pairIndex == -1 then break
    if !cur.i.overlaps second.i && !cur.i.adjacent second.i then
      ret := ret.push cur.i
      cur := second
      continue
    -- `cur.i.MergeInto(second.i)`: cannot fail here (overlapping or adjacent)
    match cur.i.mergeInto second.i with
    | .ok i => cur := { cur with i }
    | .error _ => pure ()
  return ret.push cur.i

end Intervals

end GoFV.Gen
