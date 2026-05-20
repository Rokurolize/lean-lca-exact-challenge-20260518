import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Opposites

/-!
W282: generic opposite transport for parallel-pair limit stability.

W259 isolated the `WalkingParallelPair` branch of the opposite finite-limit route.  This file
proves the formal transport theorem at the level where Lean's `Cone.op` API lives: colimit
stability of `W.op.op` over `Jᵒᵖ` implies limit stability of `W.op` over `J`.

For `boundedExactWeakEquivalence MetrizableLCA`, this removes the formal op-transport gap for
the `WalkingParallelPair` branch once the corresponding double-op colimit-stability input is
available.  It does not prove the direct colimit-stability theorem itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

universe w v u

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace OppositeWalkingParallelPairTransportW282

variable {C : Type u} [Category.{v} C]

/--
Generic formal transport: if `W.op.op` is stable under colimits of shape `Jᵒᵖ`, then `W.op`
is stable under limits of shape `J`.
-/
theorem op_isStableUnderLimitsOfShape_of_opOp_isStableUnderColimitsOfShape
    (W : MorphismProperty C) {J : Type w} [Category J]
    [W.op.op.IsStableUnderColimitsOfShape Jᵒᵖ] :
    W.op.IsStableUnderLimitsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    have hfop : W.op.op.functorCategory Jᵒᵖ (NatTrans.op f) := by
      intro j
      simpa using hf (unop j)
    have hcolimit : W.op.op φ.op :=
      MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₂.op X₁.op c₂.op c₁.op h₂.op h₁.op (NatTrans.op f) hfop φ.op (by
          intro j
          exact congrArg Quiver.Hom.op (hφ (unop j)))
    simpa using hcolimit

/-- The direct bounded exact weak-equivalence class over metrizable LCAs. -/
abbrev metrizableLCAWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0}) :=
  boundedExactWeakEquivalence MetrizableLCA.{0}

/--
The double-op colimit-stability input that feeds the generic transport theorem for the
`WalkingParallelPair` branch.
-/
abbrev MetrizableLCAWalkingParallelPairDoubleOpColimitStabilityNeeded : Prop :=
  (metrizableLCAWeakEquivalence).op.op.IsStableUnderColimitsOfShape WalkingParallelPairᵒᵖ

/-- The opposite `WalkingParallelPair` limit-stability target from W259. -/
abbrev MetrizableLCAOppositeWalkingParallelPairStabilityTarget : Prop :=
  (metrizableLCAWeakEquivalence).op.IsStableUnderLimitsOfShape WalkingParallelPair

/--
The formal `WalkingParallelPair` transport specialized to bounded exact weak equivalences.
The remaining missing theorem is the double-op colimit-stability input, not this transport.
-/
theorem metrizableLCA_oppositeWalkingParallelPairStability_of_doubleOpColimits
    (h : MetrizableLCAWalkingParallelPairDoubleOpColimitStabilityNeeded) :
    MetrizableLCAOppositeWalkingParallelPairStabilityTarget := by
  haveI := h
  exact op_isStableUnderLimitsOfShape_of_opOp_isStableUnderColimitsOfShape
    (metrizableLCAWeakEquivalence) (J := WalkingParallelPair)

/-- Machine-readable W282 frontier state. -/
structure OppositeWalkingParallelPairTransportState : Type where
  seed : String
  selectedRoute : String
  provedTransportTheorems : List String
  remainingDirectInputs : List String
  strongestConsumer : String
  productSuccessClaimed : Bool

/-- Reproducible W282 state. -/
def currentOppositeWalkingParallelPairTransportState :
    OppositeWalkingParallelPairTransportState where
  seed := "49269c75-4f70-41c7-b741-2a2399737f88"
  selectedRoute := "double-op-colimit-stability-to-opposite-limit-stability"
  provedTransportTheorems :=
    ["op_isStableUnderLimitsOfShape_of_opOp_isStableUnderColimitsOfShape",
      "metrizableLCA_oppositeWalkingParallelPairStability_of_doubleOpColimits"]
  remainingDirectInputs :=
    ["(boundedExactWeakEquivalence MetrizableLCA).op.op.IsStableUnderColimitsOfShape WalkingParallelPairᵒᵖ",
      "source-side comparison between direct WalkingParallelPairᵒᵖ colimit stability and the double-op input"]
  strongestConsumer :=
    "metrizableLCA_oppositeWalkingParallelPairStability_of_doubleOpColimits"
  productSuccessClaimed := false

theorem currentOppositeWalkingParallelPairTransportState_productSuccess :
    currentOppositeWalkingParallelPairTransportState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def oppositeWalkingParallelPairTransportDeclarationNames : List String :=
  ["op_isStableUnderLimitsOfShape_of_opOp_isStableUnderColimitsOfShape",
    "metrizableLCAWeakEquivalence",
    "MetrizableLCAWalkingParallelPairDoubleOpColimitStabilityNeeded",
    "MetrizableLCAOppositeWalkingParallelPairStabilityTarget",
    "metrizableLCA_oppositeWalkingParallelPairStability_of_doubleOpColimits",
    "currentOppositeWalkingParallelPairTransportState"]

theorem oppositeWalkingParallelPairTransportDeclarationNames_count :
    oppositeWalkingParallelPairTransportDeclarationNames.length = 6 := rfl

section Checks

#check op_isStableUnderLimitsOfShape_of_opOp_isStableUnderColimitsOfShape
#check metrizableLCAWeakEquivalence
#check MetrizableLCAWalkingParallelPairDoubleOpColimitStabilityNeeded
#check MetrizableLCAOppositeWalkingParallelPairStabilityTarget
#check metrizableLCA_oppositeWalkingParallelPairStability_of_doubleOpColimits
#check currentOppositeWalkingParallelPairTransportState
#check currentOppositeWalkingParallelPairTransportState_productSuccess
#check oppositeWalkingParallelPairTransportDeclarationNames
#check oppositeWalkingParallelPairTransportDeclarationNames_count

end Checks

end OppositeWalkingParallelPairTransportW282

end LeanLCAExactChallenge
