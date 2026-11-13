import GoFV.Proof.Witness.DSE
import GoFV.Proof.Witness.MoveSrc

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness: `VarDef` poisons only a `PAUTO` (S3, `docs/plans/false-classes.md` §5)

`f10vd` is `f10` of `test/initialize` (`InitF10.lean`) without its two `Store`s: the result `~r0`
(a `PPARAMOUT`, 16 bytes) is cleared by `v8 = Zero [16] (LocalAddr {~r0}) v7`, and the returned
memory is `v9 = VarDef {~r0} v8`:

```go
func f10vd(s *S) (r [2]*S) { r = [2]*S{}; return } // VarDef r; Zero r; VarDef r; return
```

By kernel evaluation:
* `f10vd` passes `check` and returns 16 zero bytes: the `VarDef` of the result keeps the `Zero`'s
  bytes (`Sem.varDefMem`; before S3 it made them `poison`).
* dse's checker rejects turning `v8` into `Copy v7` (`f10vdOut`): the `VarDef` of a `PPARAMOUT`
  no longer clears `v8`'s pending range (`DSE.pendStep`), and those bytes are returned.
* `VarDef` still poisons a `PAUTO`: `d` of `moveVia` (`MoveSrc.lean`) is one, `~r0` is not.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- `f10` without the `Store`s: the result is cleared, then `VarDef {~r0}` is the returned memory. -/
def f10vd : Func :=
  { f10 with
    valueTab := (((((((f10Values.set! 5 (some (mkVa 5 .LocalAddr 37 0 (some 4) p0 1 #[2, 1]))).set!
      6 (some (mkVa 6 .ArgIntReg 2 0 (some 7) (pos 2 55 24 1) 0 #[]))).set! 15 none).set! 16 none).set!
      19 none).set! 20 none).set! 23 (some (mkVa 23 .MakeResult 35 0 none (pos 2 55 24 0) 1 #[9])))
    blockTab := #[none, some (mkB 1 .Ret (pos 2 55 24 1) #[23] #[] #[] #[1, 2, 6, 5, 7, 8, 9, 23])]
    freeValues := [12, 17, 21, 22, 24, 3, 4, 14, 18, 13, 11, 10, 15, 16, 19, 20] }

/-- `f10vd` with the `Zero` `v8` eliminated as dse would (`Copy v7`). -/
def f10vdOut : Func :=
  { f10vd with
    valueTab := (f10vd.valueTab.set! 5 (some (mkVa 5 .LocalAddr 37 0 (some 4) p0 0 #[2, 1]))).set! 8
      (some (mkVa 8 .Copy 31 0 none (pos 2 55 6 1) 1 #[7])) }

/-- `f10vd` passes `check`, returns the 16 zero bytes of its cleared result, and dse's checker
rejects eliminating the `Zero` (`f10vdOut` passes `check`, so only `DSE.drel` rejects it). -/
theorem f10vd_witness :
    (check f10CheckEnv f10vd).toBool = true ∧
    returnsBlob (run Env.p1 f10Tabs f10vd f10Args {} 1) (List.replicate 16 (.b 0)) = true ∧
    (check f10CheckEnv f10vdOut).toBool = true ∧ DSE.drel f10Tabs f10vd f10vdOut = false := by
  decide +kernel

/-- `VarDef` poisons `moveVia`'s `PAUTO` `d` (aux 6) and not `f10`'s `PPARAMOUT` `~r0` (aux 4). -/
theorem varDefPoisons_witness : mvTabs.varDefPoisons 6 = true ∧ f10Tabs.varDefPoisons 4 = false := by
  decide +kernel

end GoFV.Proof.Witness
