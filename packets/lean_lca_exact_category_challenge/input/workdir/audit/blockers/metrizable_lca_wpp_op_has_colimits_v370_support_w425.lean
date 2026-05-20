import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
W425: `WalkingParallelPairᵒᵖ` colimits in `MetrizableLCA`.

The remaining W422 assumption is available directly from the local finite
colimit instance for `MetrizableLCA`: `LeanLCAExactChallenge.LCA.Cokernel`
builds cokernels and finite colimits, while mathlib's finite-shape API supplies
`HasColimitsOfShape` for finite categories such as `WalkingParallelPairᵒᵖ`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCAWppOpHasColimitsV370SupportW425

/-- The local finite-colimit instance for `MetrizableLCA` is available. -/
theorem metrizableLCA_hasFiniteColimits :
    HasFiniteColimits MetrizableLCA.{0} :=
  inferInstance

/--
The W422 shape-existence input: `MetrizableLCA` has colimits of shape
`WalkingParallelPairᵒᵖ`.
-/
theorem metrizableLCA_hasColimitsOfShape_walkingParallelPair_op :
    HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0} :=
  inferInstance

/-- One-diagram form of the WPP-op colimit existence witness. -/
theorem metrizableLCA_hasColimit_walkingParallelPair_op
    (K : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    HasColimit K :=
  inferInstance

/-- W425 checked support state. -/
structure MetrizableLCAWppOpHasColimitsV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  metrizableLcaWppOpHasColimitsResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLCAWppOpHasColimitsV370SupportState :
    MetrizableLCAWppOpHasColimitsV370SupportState where
  seed := "c42581e1a1fb650d57d2dba21ebb33b1"
  checkedConstructors :=
    ["metrizableLCA_hasFiniteColimits",
      "metrizableLCA_hasColimitsOfShape_walkingParallelPair_op",
      "metrizableLCA_hasColimit_walkingParallelPair_op"]
  metrizableLcaWppOpHasColimitsResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentMetrizableLCAWppOpHasColimitsV370SupportState_productSuccess :
    currentMetrizableLCAWppOpHasColimitsV370SupportState.productSuccessClaimed = false :=
  rfl

section Checks

#check metrizableLCA_hasFiniteColimits
#check metrizableLCA_hasColimitsOfShape_walkingParallelPair_op
#check metrizableLCA_hasColimit_walkingParallelPair_op
#check currentMetrizableLCAWppOpHasColimitsV370SupportState_productSuccess

end Checks

end MetrizableLCAWppOpHasColimitsV370SupportW425

end LeanLCAExactChallenge
