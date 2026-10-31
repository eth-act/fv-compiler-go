import GoFV.Opt.Pass
import GoFV.SSA.Alloc

/-!
# insert resched checks (`loopreschedchecks.go`)

The pass is `disabled: !buildcfg.Experiment.PreemptibleLoops` (`compile.go:490`), off in the
default build: the driver does not run it and the export has no section for it. With the
experiment on, `insertLoopReschedChecks` returns at once for `f.NoSplit` functions and for
functions without back edges (`:64-72`); those guards and `backedges` are ported. The
check insertion itself (dominance-frontier memory phis, `test`/`sched` blocks) is not ported,
so such a function is reported as unsupported.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `backedges(f)` (`loopreschedchecks.go:482`): iterative DFS from the entry over `Succs` in
order; an edge to a block that is still on the stack is a back edge. Fuel: every step pushes a
block (each at most once), consumes a successor edge, or pops. -/
def backedges (f : Func) : Array Edge := Id.run do
  -- mark: 0 notFound, 1 notExplored, 2 done
  let mut mark := (Array.replicate (f.bidLast + 1) (0 : Nat)).set! f.entry 1
  let mut stack : Array (ID × Nat) := #[(f.entry, 0)]
  let mut edges : Array Edge := #[]
  let nedges := f.blocks.foldl (fun n b => n + (f.getB b).succs.size) 0
  for _ in [0:2 * (f.bidLast + 1) + nedges + 1] do
    let some (b, i) := stack.back? | break
    let succs := (f.getB b).succs
    if h : i < succs.size then
      let e := succs[i]
      stack := stack.set! (stack.size - 1) (b, i + 1)
      let m := mark.getD e.b 0
      if m == 0 then
        mark := mark.set! e.b 1
        stack := stack.push (e.b, 0)
      else if m == 1 then
        edges := edges.push e
    else
      mark := mark.set! b 2
      stack := stack.pop
  return edges

/-- `insertLoopReschedChecks(f)` as far as ported: the `NoSplit` and no-back-edge guards. -/
def insertLoopReschedChecks (nosplit : Bool) (f : Func) : Except String Func :=
  if nosplit || (backedges f).isEmpty then pure f
  else throw "insert resched checks: GOEXPERIMENT=preemptibleloops with back edges is not ported"

/-- The `insert resched checks` pass. -/
def reschedChecksPass : Pass := Pass.ofFunc fun env f => insertLoopReschedChecks env.nosplit f

/-- `disabled: !buildcfg.Experiment.PreemptibleLoops`. -/
def reschedChecksDisabled (env : PassEnv) : Except String Bool :=
  return !(← env.flag "exp.preemptibleloops")

end GoFV.Opt
