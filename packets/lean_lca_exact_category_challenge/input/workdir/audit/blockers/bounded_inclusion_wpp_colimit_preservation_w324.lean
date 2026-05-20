import LeanLCAExactChallenge.Derived.Bounded

/-!
W324: bounded-complex inclusion preserves WPP-shaped colimits.

The W323 mapping-cone branch still needs concrete desc-assembly data, so this
file does not close that branch.  It records a positive structural fact useful
for that route: `BoundedComplexCategory.ι` preserves both `WalkingParallelPair`
and `WalkingParallelPairᵒᵖ` colimits.  This follows from the existing
boundedness closure of finite-shaped colimits.

No product-completion claim is made here.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace BoundedInclusionWppColimitPreservationW324

/-- The inclusion of bounded `MetrizableLCA` cochain complexes preserves WPP-op colimits. -/
example :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ
      (BoundedComplexCategory.ι MetrizableLCA.{0}) := by
  infer_instance

/-- The inclusion of bounded `MetrizableLCA` cochain complexes preserves WPP colimits. -/
example :
    PreservesColimitsOfShape WalkingParallelPair
      (BoundedComplexCategory.ι MetrizableLCA.{0}) := by
  infer_instance

/-- A bounded WPP-op colimit remains a colimit after inclusion into all cochain complexes. -/
def includedWalkingParallelPairOpColimit_isColimit
    {F : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c) :=
  isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc

/-- A bounded WPP colimit remains a colimit after inclusion into all cochain complexes. -/
def includedWalkingParallelPairColimit_isColimit
    {F : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c) :=
  isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc

/-- Machine-readable W324 frontier state. -/
structure BoundedInclusionWppColimitPreservationState : Type where
  seed : String
  positiveFacts : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W324 state. -/
def currentBoundedInclusionWppColimitPreservationState :
    BoundedInclusionWppColimitPreservationState where
  seed := "w324-parent-20260520T1720Z"
  positiveFacts :=
    ["BoundedComplexCategory.ι MetrizableLCA preserves WalkingParallelPairᵒᵖ colimits",
      "BoundedComplexCategory.ι MetrizableLCA preserves WalkingParallelPair colimits",
      "bounded WPP/WPP-op colimit cocones remain colimiting after inclusion"]
  remainingInputs :=
    ["W323 still needs the fixed mapping-cone cocone desc assembly data",
      "this positive preservation fact does not by itself construct the left cochain or mappingCone.desc equations"]
  productSuccessClaimed := false

theorem currentBoundedInclusionWppColimitPreservationState_productSuccess :
    currentBoundedInclusionWppColimitPreservationState.productSuccessClaimed = false := rfl

section Checks

#check includedWalkingParallelPairOpColimit_isColimit
#check includedWalkingParallelPairColimit_isColimit
#check currentBoundedInclusionWppColimitPreservationState
#check currentBoundedInclusionWppColimitPreservationState_productSuccess
#check BoundedComplexCategory.ι
#check preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape

end Checks

end BoundedInclusionWppColimitPreservationW324

end LeanLCAExactChallenge
