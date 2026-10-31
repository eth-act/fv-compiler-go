import GoFV.SSA.Sem.Int

/-!
# Comparisons, booleans, select, bounds checks (`docs/plans/semantics.md` §4.4)
-/

namespace GoFV.SSA.Sem

namespace Val

/-- The boolean of a `bool` value. -/
def asBool : Val → Option Bool
  | .bool b => some b
  | _ => none

end Val

/-- A unary boolean op. -/
@[inline] def bool1 (f : Bool → Bool) : List Val → Val
  | [a] => match a.asBool with
    | some x => .bool (f x)
    | none => .poison
  | _ => .poison

/-- A binary boolean op (both sides evaluated: no short circuit). -/
@[inline] def bool2 (f : Bool → Bool → Bool) : List Val → Val
  | [a, b] => match a.asBool, b.asBool with
    | some x, some y => .bool (f x y)
    | _, _ => .poison
  | _ => .poison

namespace Cmp

def eq (w : Width) : List Val → Val := int2 w fun x y => .bool (x == y)
def neq (w : Width) : List Val → Val := int2 w fun x y => .bool (x != y)
def less (w : Width) : List Val → Val := int2 w fun x y => .bool (x.slt y)
def lessU (w : Width) : List Val → Val := int2 w fun x y => .bool (x.ult y)
def leq (w : Width) : List Val → Val := int2 w fun x y => .bool (x.sle y)
def leqU (w : Width) : List Val → Val := int2 w fun x y => .bool (x.ule y)

def andB : List Val → Val := bool2 (· && ·)
def orB : List Val → Val := bool2 (· || ·)
def eqB : List Val → Val := bool2 (· == ·)
def neqB : List Val → Val := bool2 (· != ·)
def not : List Val → Val := bool1 (!·)

/-- `CondSelect x y c` = `c ? x : y`; the unselected arm may be `poison` (§3.5). -/
def condSelect : List Val → Val
  | [x, y, c] => match c.asBool with
    | some true => x
    | some false => y
    | none => .poison
  | _ => .poison

/-- `IsInBounds i n` = `0 ≤ i < n` and `IsSliceInBounds i n` = `0 ≤ i ≤ n` (`slice`): `n ≥ 0`
is guaranteed (gO 502-503); a negative `n` ⇒ `poison`. Arguments have one width. -/
def inBounds (slice : Bool) : List Val → Val
  | [.int w i, n] => match n.asInt w with
    | some n =>
      if n.msb then .poison
      else .bool (if slice then i.ule n else i.ult n)
    | none => .poison
  | _ => .poison

/-- `SpectreIndex i n` = `i` if `0 ≤ i < n`, else 0; `SpectreSliceIndex` with `≤` (gO 590). -/
def spectreIndex (slice : Bool) : List Val → Val
  | [.int w i, n] => match n.asInt w with
    | some n => .int w (if (if slice then i.ule n else i.ult n) then i else 0)
    | none => .poison
  | _ => .poison

end Cmp

end GoFV.SSA.Sem
