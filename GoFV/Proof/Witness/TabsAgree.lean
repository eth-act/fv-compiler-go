import GoFV.Proof.TabsAgree
import GoFV.Proof.Witness.Clamp

/-!
# Witness: `run_tabsAgree` on `clamp` with extended tables

`clampTabs` extended the way `expand calls` extends tables (a new type and a type aux at fresh
numbers) satisfies `tabsAgree` (`decide +kernel`), so `clamp`'s runs carry over unchanged
(`clamp_run_ext`). A new `PAUTO` variable (what `decompose builtin` adds for a split slot) is a
new frame allocation of every run, and the check rejects it (`clampTabs_pauto`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

/-- `clampTabs` with a new type (`[2]int`, number 34) and a type aux naming it (number 7). -/
def clampTabsExt : Tables :=
  { clampTabs with
    types := clampTabs.types.push (some (mkT .ARRAY (some 16) "[2]int" (.array 2 2)))
    auxes := clampTabs.auxes.push
      (some { fmt := GoStr.ofString "[2]int", kind := .type 34 }) }

theorem clampTabsExt_agree : GoFV.Opt.tabsAgree clampTabs clampTabsExt clamp = true := by
  decide +kernel

/-- `clamp_run` in the extended tables, by `run_tabsAgree`. -/
theorem clamp_run_ext :
    returnsInt (run Env.p1 clampTabsExt clamp (clampArgs 5) {} 3) 5 = true := by
  rw [run_tabsAgree clampTabsExt_agree]
  exact clamp_run.1

/-- `clampTabs` with a new `PAUTO` variable: not accepted. -/
theorem clampTabs_pauto :
    GoFV.Opt.tabsAgree clampTabs
      { clampTabs with auxes := clampTabs.auxes.push (some (paramName "x.ptr" .PAUTO 0)) }
      clamp = false := by
  decide +kernel

end GoFV.Proof.Witness
