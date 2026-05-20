import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Opposites

/-!
W283: direct colimit-to-opposite-limit transport for shape stability.

W282 proved a double-op variant of the `WalkingParallelPair` transport.  Inspecting
`Mathlib.CategoryTheory.Limits.Opposites` shows that the sharper theorem is available directly:
`coconeLeftOpOfCone` turns a limit cone in `Cᵒᵖ` into a colimit cocone in `C`, and
`NatTrans.leftOp` gives the natural transformation with the correct orientation.

This closes the formal op-transport part of the W259 `WalkingParallelPair` branch.  The
remaining non-formal input is direct colimit stability of `boundedExactWeakEquivalence
MetrizableLCA` for shape `WalkingParallelPairᵒᵖ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

universe w v u

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace OppositeDirectColimitToLimitTransportW283

variable {C : Type u} [Category.{v} C]

/--
If `W` is stable under colimits of shape `Jᵒᵖ`, then `W.op` is stable under limits of shape
`J`.  This is the direct formal transport needed for opposite equalizer-style routes.
-/
theorem op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op
    (W : MorphismProperty C) {J : Type w} [Category J]
    [W.IsStableUnderColimitsOfShape Jᵒᵖ] :
    W.op.IsStableUnderLimitsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    have hfop : W.functorCategory (Jᵒᵖ) (NatTrans.leftOp f) := by
      intro j
      simpa using hf (unop j)
    exact
      MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₂.leftOp X₁.leftOp (coconeLeftOpOfCone c₂) (coconeLeftOpOfCone c₁)
        (isColimitCoconeLeftOpOfCone X₂ h₂) (isColimitCoconeLeftOpOfCone X₁ h₁)
        (NatTrans.leftOp f) hfop φ.unop (by
          intro j
          simpa only [coconeLeftOpOfCone_ι_app, NatTrans.leftOp_app] using
            congrArg Quiver.Hom.unop (hφ (unop j)))

/-- The direct bounded exact weak-equivalence class over metrizable LCAs. -/
abbrev metrizableLCAWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0}) :=
  boundedExactWeakEquivalence MetrizableLCA.{0}

/-- The direct colimit-stability input that remains after W283. -/
abbrev MetrizableLCAWalkingParallelPairOpColimitStabilityNeeded : Prop :=
  (metrizableLCAWeakEquivalence).IsStableUnderColimitsOfShape WalkingParallelPairᵒᵖ

/-- The opposite `WalkingParallelPair` limit-stability target from W259. -/
abbrev MetrizableLCAOppositeWalkingParallelPairStabilityTarget : Prop :=
  (metrizableLCAWeakEquivalence).op.IsStableUnderLimitsOfShape WalkingParallelPair

/--
Specialized consumer for the W259 `WalkingParallelPair` branch: a direct
`WalkingParallelPairᵒᵖ` colimit-stability theorem now immediately gives the opposite
`WalkingParallelPair` limit-stability field.
-/
theorem metrizableLCA_oppositeWalkingParallelPairStability_of_directColimits
    (h : MetrizableLCAWalkingParallelPairOpColimitStabilityNeeded) :
    MetrizableLCAOppositeWalkingParallelPairStabilityTarget := by
  haveI := h
  exact op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op
    (metrizableLCAWeakEquivalence) (J := WalkingParallelPair)

/-- Machine-readable W283 frontier state. -/
structure OppositeDirectColimitToLimitTransportState : Type where
  seed : String
  selectedRoute : String
  provedTransportTheorems : List String
  remainingDirectInputs : List String
  strongestConsumer : String
  productSuccessClaimed : Bool

/-- Reproducible W283 state. -/
def currentOppositeDirectColimitToLimitTransportState :
    OppositeDirectColimitToLimitTransportState where
  seed := "ad4f4cb6-9684-4edb-bcdf-5b227265f2aa"
  selectedRoute := "direct-colimit-stability-to-opposite-limit-stability"
  provedTransportTheorems :=
    ["op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op",
      "metrizableLCA_oppositeWalkingParallelPairStability_of_directColimits"]
  remainingDirectInputs :=
    ["(boundedExactWeakEquivalence MetrizableLCA).IsStableUnderColimitsOfShape WalkingParallelPairᵒᵖ"]
  strongestConsumer :=
    "metrizableLCA_oppositeWalkingParallelPairStability_of_directColimits"
  productSuccessClaimed := false

theorem currentOppositeDirectColimitToLimitTransportState_productSuccess :
    currentOppositeDirectColimitToLimitTransportState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def oppositeDirectColimitToLimitTransportDeclarationNames : List String :=
  ["op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op",
    "metrizableLCAWeakEquivalence",
    "MetrizableLCAWalkingParallelPairOpColimitStabilityNeeded",
    "MetrizableLCAOppositeWalkingParallelPairStabilityTarget",
    "metrizableLCA_oppositeWalkingParallelPairStability_of_directColimits",
    "currentOppositeDirectColimitToLimitTransportState"]

theorem oppositeDirectColimitToLimitTransportDeclarationNames_count :
    oppositeDirectColimitToLimitTransportDeclarationNames.length = 6 := rfl

section Checks

#check op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op
#check metrizableLCAWeakEquivalence
#check MetrizableLCAWalkingParallelPairOpColimitStabilityNeeded
#check MetrizableLCAOppositeWalkingParallelPairStabilityTarget
#check metrizableLCA_oppositeWalkingParallelPairStability_of_directColimits
#check currentOppositeDirectColimitToLimitTransportState
#check currentOppositeDirectColimitToLimitTransportState_productSuccess
#check oppositeDirectColimitToLimitTransportDeclarationNames
#check oppositeDirectColimitToLimitTransportDeclarationNames_count

end Checks

end OppositeDirectColimitToLimitTransportW283

end LeanLCAExactChallenge
