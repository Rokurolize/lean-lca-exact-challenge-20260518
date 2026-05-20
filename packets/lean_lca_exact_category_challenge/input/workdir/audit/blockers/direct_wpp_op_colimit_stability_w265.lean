import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Opposites

/-!
W265: direct `WalkingParallelPairᵒᵖ` colimit-stability boundary.

W283 closes the formal transport from direct `WalkingParallelPairᵒᵖ` colimit stability of
`boundedExactWeakEquivalence MetrizableLCA` to `WalkingParallelPair` limit stability of the
opposite morphism property.  This file checks the smallest remaining direct input boundary.

The direct closure theorem is not currently available from the finite-product route.  The missing
mathematical ingredients are the `WalkingParallelPairᵒᵖ` coequalizer comparison for mapping cones
after bounded inclusion, and closure of `exactAcyclic MetrizableLCA` under those coequalizers.
Once those give the constructor condition below, the W283-style transport consumes it immediately.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

universe w v u

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace DirectWalkingParallelPairOpColimitStabilityW265

variable {C : Type u} [Category.{v} C]

/--
W283's formal transport: direct colimit stability over `Jᵒᵖ` gives opposite limit stability over
`J`.  The W283 audit file itself is not importable as a Lake module, so this file checks the same
transport shape locally to make the downstream consumer executable.
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

/-- The exact direct stability target left open after W283. -/
abbrev MetrizableLCADirectWalkingParallelPairOpColimitStabilityTarget : Prop :=
  (metrizableLCAWeakEquivalence).IsStableUnderColimitsOfShape WalkingParallelPairᵒᵖ

/-- The opposite `WalkingParallelPair` stability target consumed by W259/W283. -/
abbrev MetrizableLCAOppositeWalkingParallelPairLimitStabilityTarget : Prop :=
  (metrizableLCAWeakEquivalence).op.IsStableUnderLimitsOfShape WalkingParallelPair

/--
The constructor-level condition for direct `WalkingParallelPairᵒᵖ` colimit stability.

This is deliberately stated in the exact shape required by
`MorphismProperty.IsStableUnderColimitsOfShape.mk`: a future mapping-cone/coequalizer theorem can
fill this condition without any further localization or opposite-category API.
-/
abbrev MetrizableLCADirectWalkingParallelPairOpColimitConditionInput : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂),
      (metrizableLCAWeakEquivalence).functorCategory WalkingParallelPairᵒᵖ f →
        ∀ (φ : c₁.pt ⟶ c₂.pt),
          (∀ j : WalkingParallelPairᵒᵖ,
            c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) →
              metrizableLCAWeakEquivalence φ

/--
No categorical wrapper remains above the direct constructor condition: it is exactly the mathlib
stability class needed by the W283 transport.
-/
theorem metrizableLCA_directWalkingParallelPairOpColimitStability_of_conditionInput
    (h : MetrizableLCADirectWalkingParallelPairOpColimitConditionInput) :
    MetrizableLCADirectWalkingParallelPairOpColimitStabilityTarget :=
  MorphismProperty.IsStableUnderColimitsOfShape.mk h

/-- W283-style specialized consumer for the remaining direct input. -/
theorem metrizableLCA_oppositeWalkingParallelPairLimitStability_of_directColimits
    (h : MetrizableLCADirectWalkingParallelPairOpColimitStabilityTarget) :
    MetrizableLCAOppositeWalkingParallelPairLimitStabilityTarget := by
  haveI := h
  exact op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op
    (metrizableLCAWeakEquivalence) (J := WalkingParallelPair)

/--
Consumer from the smallest checked direct theorem boundary into the W283-style transport target.
-/
theorem metrizableLCA_oppositeWalkingParallelPairLimitStability_of_conditionInput
    (h : MetrizableLCADirectWalkingParallelPairOpColimitConditionInput) :
    MetrizableLCAOppositeWalkingParallelPairLimitStabilityTarget :=
  metrizableLCA_oppositeWalkingParallelPairLimitStability_of_directColimits
    (metrizableLCA_directWalkingParallelPairOpColimitStability_of_conditionInput h)

/-- Machine-readable W265 frontier state. -/
structure DirectWalkingParallelPairOpColimitStabilityState : Type where
  seed : String
  selectedRoute : String
  directTarget : String
  checkedBoundary : String
  missingComparisonTheorem : String
  missingClosureTheorem : String
  w283TransportConsumer : String
  importedAuditModulesAvailable : Bool
  productSuccessClaimed : Bool

/-- Reproducible W265 boundary state. -/
def currentDirectWalkingParallelPairOpColimitStabilityState :
    DirectWalkingParallelPairOpColimitStabilityState where
  seed := "w265-20260520T143521Z-48927ec0e42ce498"
  selectedRoute := "direct WalkingParallelPair.op colimit stability feeding W283 transport"
  directTarget :=
    "(boundedExactWeakEquivalence MetrizableLCA).IsStableUnderColimitsOfShape WalkingParallelPairᵒᵖ"
  checkedBoundary :=
    "MetrizableLCADirectWalkingParallelPairOpColimitConditionInput"
  missingComparisonTheorem :=
    "mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison"
  missingClosureTheorem :=
    "exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure"
  w283TransportConsumer :=
    "metrizableLCA_oppositeWalkingParallelPairLimitStability_of_conditionInput"
  importedAuditModulesAvailable := false
  productSuccessClaimed := false

theorem currentDirectWalkingParallelPairOpColimitStabilityState_productSuccess :
    currentDirectWalkingParallelPairOpColimitStabilityState.productSuccessClaimed = false := rfl

theorem currentDirectWalkingParallelPairOpColimitStabilityState_auditImportUnavailable :
    currentDirectWalkingParallelPairOpColimitStabilityState.importedAuditModulesAvailable = false :=
  rfl

/-- Named declarations produced by this audit file. -/
def directWalkingParallelPairOpColimitStabilityDeclarationNames : List String :=
  ["op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op",
    "metrizableLCAWeakEquivalence",
    "MetrizableLCADirectWalkingParallelPairOpColimitStabilityTarget",
    "MetrizableLCAOppositeWalkingParallelPairLimitStabilityTarget",
    "MetrizableLCADirectWalkingParallelPairOpColimitConditionInput",
    "metrizableLCA_directWalkingParallelPairOpColimitStability_of_conditionInput",
    "metrizableLCA_oppositeWalkingParallelPairLimitStability_of_directColimits",
    "metrizableLCA_oppositeWalkingParallelPairLimitStability_of_conditionInput",
    "currentDirectWalkingParallelPairOpColimitStabilityState"]

theorem directWalkingParallelPairOpColimitStabilityDeclarationNames_count :
    directWalkingParallelPairOpColimitStabilityDeclarationNames.length = 9 := rfl

section Checks

#check op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op
#check metrizableLCAWeakEquivalence
#check MetrizableLCADirectWalkingParallelPairOpColimitStabilityTarget
#check MetrizableLCAOppositeWalkingParallelPairLimitStabilityTarget
#check MetrizableLCADirectWalkingParallelPairOpColimitConditionInput
#check metrizableLCA_directWalkingParallelPairOpColimitStability_of_conditionInput
#check metrizableLCA_oppositeWalkingParallelPairLimitStability_of_directColimits
#check metrizableLCA_oppositeWalkingParallelPairLimitStability_of_conditionInput
#check currentDirectWalkingParallelPairOpColimitStabilityState
#check currentDirectWalkingParallelPairOpColimitStabilityState_productSuccess
#check currentDirectWalkingParallelPairOpColimitStabilityState_auditImportUnavailable
#check directWalkingParallelPairOpColimitStabilityDeclarationNames
#check directWalkingParallelPairOpColimitStabilityDeclarationNames_count
#check BoundedFiniteProducts.isStableUnderFiniteProducts_metrizableLCA

end Checks

end DirectWalkingParallelPairOpColimitStabilityW265

end LeanLCAExactChallenge
