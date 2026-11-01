import GoFV.Proof.Witness.DecPhis

/-!
# The witnesses of `decPhis_refines` are the phi stage's outputs

`formatBoolOut`/`pairOut` (`GoFV/Proof/Witness/FormatBool.lean`) are what
`Decompose.phiStage` computes from `formatBool`/`pair`, in unchanged tables (checked by running
the stage; its state uses `Std.HashMap`, which the kernel does not evaluate).
-/

open GoFV.SSA GoFV.Opt GoFV.Proof.Witness

def stageIs (tabs : Tables) (builtin : Bool) (f g : Func) : Bool :=
  match Decompose.phiStage (fbPassEnv "decompose" tabs) builtin f with
  | .ok (t, g') => g' == g && t.types == tabs.types && t.auxes == tabs.auxes && t.slots == tabs.slots
  | .error _ => false

#guard stageIs formatBoolTabs true formatBool formatBoolOut
#guard stageIs pairTabs false pair pairOut
