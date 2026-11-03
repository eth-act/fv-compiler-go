import GoFV.Opt.Pass
import GoFV.SSA.Edges

/-!
# critical (`critical.go:10-112`)

`critical` (docs/PASSES2.md, critical, issue #403): for each block of `f.Blocks` by index,
including the splitter blocks appended on the way, with more than one predecessor: if it has
exactly one phi, the incoming edges whose phi argument is the same value share one splitter
(the first edge allocates it at its predecessor's `Pos`; a later edge is redirected to it and
its predecessor and phi argument swap-removed, without advancing); otherwise every edge from a
non-`Plain` predecessor gets its own `Plain` splitter.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `critical(f)`. -/
def critical (f : Func) : Except String Func := do
  let mut blocks : Array (Option ID) := Array.replicate (f.vidLast + 1) none
  let mut f := f
  let mut j := 0
  let edges := f.blocks.foldl (fun n b => n + (f.getB b).preds.size) 0
  for _ in [0:f.blocks.size + 3 * edges + 4] do
    if h : j < f.blocks.size then
      let b := f.blocks[j]
      j := j + 1
      if (f.getB b).preds.size ≤ 1 then continue
      let mut phi : Option ID := none
      for v in (f.getB b).values do
        if (f.getV v).op == .Phi then
          if phi.isSome then
            phi := none
            break
          phi := some v
      if let some p := phi then
        for a in (f.getV p).args do
          blocks := blocks.set! a none
      let mut i := 0
      for _ in [0:2 * (f.getB b).preds.size + 2] do
        let preds := (f.getB b).preds
        if hi : i < preds.size then
          let e := preds[i]
          let p := e.b
          let pi := e.i
          if (f.getB p).kind == .Plain then
            i := i + 1
            continue
          let mut d : ID := 0
          let mut reused := false
          match phi with
          | some ph =>
            let some argID := (f.getV ph).args[i]?
              | throw s!"critical: phi v{ph} has no argument {i}"
            match blocks[argID]! with
            | none =>
              let (f', d') := f.newBlock .Plain
              let pos := (f'.getB p).pos
              f := f'.modB d' fun x => { x with pos }
              d := d'
              blocks := blocks.set! argID (some d')
            | some d' =>
              d := d'
              reused := true
          | none =>
            let (f', d') := f.newBlock .Plain
            let pos := (f'.getB p).pos
            f := f'.modB d' fun x => { x with pos }
            d := d'
          if reused then
            let n := (f.getB d).preds.size
            f := f.modB p fun x => { x with succs := x.succs.set! pi ⟨d, n⟩ }
            f := f.modB d fun x => { x with preds := x.preds.push ⟨p, pi⟩ }
            f := f.removePred b i
            f := f.removePhiArg b phi.get! i
          else
            f := f.modB p fun x => { x with succs := x.succs.set! pi ⟨d, 0⟩ }
            f := f.modB b fun x => { x with preds := x.preds.set! i ⟨d, 0⟩ }
            f := f.modB d fun x => { x with preds := x.preds.push ⟨p, pi⟩,
                                             succs := x.succs.push ⟨b, i⟩ }
            i := i + 1
        else break
    else break
  return f

/-- The `critical` pass. -/
def criticalPass : Pass := Pass.ofFunc fun _ f => critical f

end GoFV.Opt
