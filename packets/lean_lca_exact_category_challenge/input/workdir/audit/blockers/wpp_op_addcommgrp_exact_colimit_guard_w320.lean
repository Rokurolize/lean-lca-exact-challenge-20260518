import LeanLCAExactChallenge
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected

/-!
W320: guard against treating WPP-op colimits in `AddCommGrpCat` as automatically
exact.

The W319 additive boundary is useful as a local reduction, but it must not be
mistaken for an available mathlib instance.  `AddCommGrpCat` has exact filtered
colimits (`AB5`), while `WalkingParallelPairᵒᵖ` is connected but not filtered in
the relevant sense.  The guarded `#synth` probes below record that mathlib does
not supply exact colimits of this finite coequalizer-shaped form.

This file is a negative guard, not a product-completion claim.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
error: failed to synthesize
  HasExactColimitsOfShape WalkingParallelPairᵒᵖ AddCommGrpCat

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth HasExactColimitsOfShape WalkingParallelPairᵒᵖ AddCommGrpCat

/--
error: failed to synthesize
  HasExactColimitsOfShape WalkingParallelPair AddCommGrpCat

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth HasExactColimitsOfShape WalkingParallelPair AddCommGrpCat

example : IsConnected WalkingParallelPairᵒᵖ := by infer_instance
example : IsConnected WalkingParallelPair := by infer_instance

/-- Machine-readable W320 negative-guard state. -/
structure WppOpAddCommGrpExactColimitGuardState : Type where
  seed : String
  checkedNegativeGuard : String
  positiveFacts : List String
  productSuccessClaimed : Bool

/-- Reproducible W320 state. -/
def currentWppOpAddCommGrpExactColimitGuardState :
    WppOpAddCommGrpExactColimitGuardState where
  seed := "w320-parent-20260520T1714Z"
  checkedNegativeGuard :=
    "no synthesized HasExactColimitsOfShape instance for WalkingParallelPair or its opposite in AddCommGrpCat"
  positiveFacts :=
    ["IsConnected WalkingParallelPair",
      "IsConnected WalkingParallelPairᵒᵖ"]
  productSuccessClaimed := false

theorem currentWppOpAddCommGrpExactColimitGuardState_productSuccess :
    currentWppOpAddCommGrpExactColimitGuardState.productSuccessClaimed = false := rfl

section Checks

#check currentWppOpAddCommGrpExactColimitGuardState
#check currentWppOpAddCommGrpExactColimitGuardState_productSuccess
#check isConnected_op
#check parallel_pair_connected

end Checks

end LeanLCAExactChallenge
