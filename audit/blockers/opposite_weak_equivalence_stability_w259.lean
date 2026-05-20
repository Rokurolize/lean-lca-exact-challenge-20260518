import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Limits.Opposites

/-!
W259: opposite weak-equivalence stability boundary.

W255 reduced finite limits in `((boundedExactWeakEquivalence MetrizableLCA).op).Localization`
to finite products plus `WalkingParallelPair` limits for the opposite weak-equivalence class.
This file isolates those two stability fields. The direct finite-product stability theorem is
available, but it is not by itself the opposite finite-product input: products in the opposite
ask for direct finite-coproduct stability, and `WalkingParallelPair` limits in the opposite ask
for the corresponding direct colimit/coequalizer stability and an opposite-transport lemma.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeWeakEquivalenceStabilityW259

/-- The concrete opposite bounded weak-equivalence class requested by W259. -/
abbrev metrizableLCA_oppositeWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ :=
  (boundedExactWeakEquivalence MetrizableLCA.{0}).op

/-- The requested opposite finite-product stability target. -/
abbrev MetrizableLCAOppositeFiniteProductStabilityTarget : Prop :=
  (metrizableLCA_oppositeWeakEquivalence).IsStableUnderFiniteProducts

/-- The requested opposite `WalkingParallelPair` stability target. -/
abbrev MetrizableLCAOppositeWalkingParallelPairStabilityTarget : Prop :=
  (metrizableLCA_oppositeWeakEquivalence).IsStableUnderLimitsOfShape WalkingParallelPair

/-- The two W255 stability fields, isolated as one reusable package. -/
structure MetrizableLCAOppositeWeakEquivalenceStabilityFields : Prop where
  finiteProducts : MetrizableLCAOppositeFiniteProductStabilityTarget
  walkingParallelPair : MetrizableLCAOppositeWalkingParallelPairStabilityTarget

/-- The direct finite-product stability theorem already present in the project. -/
theorem metrizableLCA_directFiniteProductStability_available :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteProducts :=
  BoundedFiniteProducts.isStableUnderFiniteProducts_metrizableLCA

/--
Direct finite-coproduct stability is the source-side hypothesis that would transport to
finite-product stability of the opposite weak-equivalence class.
-/
abbrev MetrizableLCADirectFiniteCoproductStabilityNeeded : Prop :=
  (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteCoproducts

/--
Direct `WalkingParallelPairᵒᵖ` colimit stability is the source-side hypothesis that would
transport to `WalkingParallelPair` limit stability of the opposite weak-equivalence class.
-/
abbrev MetrizableLCADirectWalkingParallelPairOpColimitStabilityNeeded : Prop :=
  (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
    WalkingParallelPairᵒᵖ

/-- The exact finite-product opposite-transport lemma still needed. -/
abbrev MetrizableLCAFiniteCoproductToOppositeFiniteProductTransport : Prop :=
  MetrizableLCADirectFiniteCoproductStabilityNeeded →
    MetrizableLCAOppositeFiniteProductStabilityTarget

/-- The exact `WalkingParallelPair` opposite-transport lemma still needed. -/
abbrev MetrizableLCAWalkingParallelPairColimitToOppositeLimitTransport : Prop :=
  MetrizableLCADirectWalkingParallelPairOpColimitStabilityNeeded →
    MetrizableLCAOppositeWalkingParallelPairStabilityTarget

/--
The shortest transport package that would discharge the two W255 stability fields.
This intentionally keeps the direct closure theorems separate from the generic opposite
transport lemmas, so later work can attack either side independently.
-/
structure MetrizableLCAOppositeWeakEquivalenceStabilityTransportInputs : Prop where
  directFiniteCoproducts : MetrizableLCADirectFiniteCoproductStabilityNeeded
  finiteCoproductsToOppositeFiniteProducts :
    MetrizableLCAFiniteCoproductToOppositeFiniteProductTransport
  directWalkingParallelPairOpColimits :
    MetrizableLCADirectWalkingParallelPairOpColimitStabilityNeeded
  walkingParallelPairColimitsToOppositeLimits :
    MetrizableLCAWalkingParallelPairColimitToOppositeLimitTransport

/-- Conditional finite-product stability for the opposite weak-equivalence class. -/
theorem metrizableLCA_oppositeFiniteProductStability_of_transportInputs
    (h : MetrizableLCAOppositeWeakEquivalenceStabilityTransportInputs) :
    MetrizableLCAOppositeFiniteProductStabilityTarget :=
  h.finiteCoproductsToOppositeFiniteProducts h.directFiniteCoproducts

/-- Conditional `WalkingParallelPair` stability for the opposite weak-equivalence class. -/
theorem metrizableLCA_oppositeWalkingParallelPairStability_of_transportInputs
    (h : MetrizableLCAOppositeWeakEquivalenceStabilityTransportInputs) :
    MetrizableLCAOppositeWalkingParallelPairStabilityTarget :=
  h.walkingParallelPairColimitsToOppositeLimits h.directWalkingParallelPairOpColimits

/-- The two requested stability fields, discharged from the narrowed transport package. -/
theorem metrizableLCA_oppositeWeakEquivalenceStabilityFields_of_transportInputs
    (h : MetrizableLCAOppositeWeakEquivalenceStabilityTransportInputs) :
    MetrizableLCAOppositeWeakEquivalenceStabilityFields where
  finiteProducts := metrizableLCA_oppositeFiniteProductStability_of_transportInputs h
  walkingParallelPair := metrizableLCA_oppositeWalkingParallelPairStability_of_transportInputs h

/-- Machine-readable boundary state for this worker. -/
structure OppositeWeakEquivalenceStabilityState : Type where
  seed : String
  selectedRoute : String
  directAvailable : List String
  targetStabilityFields : List String
  missingDirectClosureTheorems : List String
  missingOppositeTransportTheorems : List String
  strongestConsumer : String
  productSuccessClaimed : Bool

/-- Reproducible W259 boundary state. -/
def currentOppositeWeakEquivalenceStabilityState :
    OppositeWeakEquivalenceStabilityState where
  seed := "e9c4d9aa-281c-4caf-9ab2-a4ac20bc56cb"
  selectedRoute :=
    "opposite stability via direct finite-coproduct/coequalizer stability plus op transport"
  directAvailable :=
    ["BoundedFiniteProducts.isStableUnderFiniteProducts_metrizableLCA"]
  targetStabilityFields :=
    ["((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderFiniteProducts",
      "((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderLimitsOfShape WalkingParallelPair"]
  missingDirectClosureTheorems :=
    ["boundedExactWeakEquivalence_metrizableLCA_finiteCoproducts",
      "boundedExactWeakEquivalence_metrizableLCA_walkingParallelPairOpColimits"]
  missingOppositeTransportTheorems :=
    ["finiteCoproductStability_to_oppositeFiniteProductStability",
      "walkingParallelPairOpColimitStability_to_oppositeWalkingParallelPairLimitStability"]
  strongestConsumer :=
    "metrizableLCA_oppositeWeakEquivalenceStabilityFields_of_transportInputs"
  productSuccessClaimed := false

theorem currentOppositeWeakEquivalenceStabilityState_productSuccess :
    currentOppositeWeakEquivalenceStabilityState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def oppositeWeakEquivalenceStabilityDeclarationNames : List String :=
  ["metrizableLCA_oppositeWeakEquivalence",
    "MetrizableLCAOppositeFiniteProductStabilityTarget",
    "MetrizableLCAOppositeWalkingParallelPairStabilityTarget",
    "MetrizableLCAOppositeWeakEquivalenceStabilityFields",
    "metrizableLCA_directFiniteProductStability_available",
    "MetrizableLCADirectFiniteCoproductStabilityNeeded",
    "MetrizableLCADirectWalkingParallelPairOpColimitStabilityNeeded",
    "MetrizableLCAFiniteCoproductToOppositeFiniteProductTransport",
    "MetrizableLCAWalkingParallelPairColimitToOppositeLimitTransport",
    "MetrizableLCAOppositeWeakEquivalenceStabilityTransportInputs",
    "metrizableLCA_oppositeFiniteProductStability_of_transportInputs",
    "metrizableLCA_oppositeWalkingParallelPairStability_of_transportInputs",
    "metrizableLCA_oppositeWeakEquivalenceStabilityFields_of_transportInputs",
    "currentOppositeWeakEquivalenceStabilityState"]

theorem oppositeWeakEquivalenceStabilityDeclarationNames_count :
    oppositeWeakEquivalenceStabilityDeclarationNames.length = 14 := rfl

section Checks

#check metrizableLCA_oppositeWeakEquivalence
#check MetrizableLCAOppositeFiniteProductStabilityTarget
#check MetrizableLCAOppositeWalkingParallelPairStabilityTarget
#check MetrizableLCAOppositeWeakEquivalenceStabilityFields
#check metrizableLCA_directFiniteProductStability_available
#check BoundedFiniteProducts.isStableUnderFiniteProducts_metrizableLCA
#check MetrizableLCADirectFiniteCoproductStabilityNeeded
#check MetrizableLCADirectWalkingParallelPairOpColimitStabilityNeeded
#check MetrizableLCAFiniteCoproductToOppositeFiniteProductTransport
#check MetrizableLCAWalkingParallelPairColimitToOppositeLimitTransport
#check MetrizableLCAOppositeWeakEquivalenceStabilityTransportInputs
#check metrizableLCA_oppositeFiniteProductStability_of_transportInputs
#check metrizableLCA_oppositeWalkingParallelPairStability_of_transportInputs
#check metrizableLCA_oppositeWeakEquivalenceStabilityFields_of_transportInputs
#check currentOppositeWeakEquivalenceStabilityState
#check currentOppositeWeakEquivalenceStabilityState_productSuccess
#check oppositeWeakEquivalenceStabilityDeclarationNames
#check oppositeWeakEquivalenceStabilityDeclarationNames_count

end Checks

end OppositeWeakEquivalenceStabilityW259

end LeanLCAExactChallenge
