import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Opposites

/-!
Opposite source finite-limit boundary.

This file records the source-side finite-limit input for the opposite finite-colimits
route. It does not claim finite colimits for `MetrizableLCA`; it isolates the local
remaining package as `HasFiniteColimits MetrizableLCA`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace OppositeSourceFiniteLimitsW234

variable (C : Type u) [Category.{v} C] [Preadditive C]

/--
Finite colimits in the exact category give finite limits on the opposite of the bounded
complex source.
-/
theorem boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits [HasFiniteColimits C] :
    HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits (BoundedComplexCategory C) := inferInstance
  exact Limits.hasFiniteColimits_opposite_iff.mp inferInstance

/--
The opposite source has finite products once the original exact category has finite
colimits.
-/
theorem boundedComplexOp_hasFiniteProducts_of_sourceFiniteColimits [HasFiniteColimits C] :
    HasFiniteProducts (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ :=
    boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits C
  infer_instance

/--
The opposite source has equalizers once the original exact category has finite colimits.
-/
theorem boundedComplexOp_hasEqualizers_of_sourceFiniteColimits [HasFiniteColimits C] :
    HasEqualizers (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ :=
    boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits C
  infer_instance

/--
Finite-colimit packaging for the source is the remaining local input when this route is
specialized to `MetrizableLCA`.
-/
structure SourceFiniteColimitInput : Prop where
  finiteColimits : HasFiniteColimits C

/-- Wrapped finite-limit consumer for callers that carry the source input as one field. -/
theorem boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput
    (h : SourceFiniteColimitInput C) :
    HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits C := h.finiteColimits
  exact boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits C

/-- Wrapped finite-product consumer for the opposite equalizer route. -/
theorem boundedComplexOp_hasFiniteProducts_of_sourceFiniteColimitInput
    (h : SourceFiniteColimitInput C) :
    HasFiniteProducts (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits C := h.finiteColimits
  exact boundedComplexOp_hasFiniteProducts_of_sourceFiniteColimits C

/-- Wrapped equalizer consumer for the opposite equalizer route. -/
theorem boundedComplexOp_hasEqualizers_of_sourceFiniteColimitInput
    (h : SourceFiniteColimitInput C) :
    HasEqualizers (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits C := h.finiteColimits
  exact boundedComplexOp_hasEqualizers_of_sourceFiniteColimits C

/--
The standard finite-colimits constructor that can close the source input once initial
objects and pushouts are packaged for the concrete category.
-/
theorem sourceFiniteColimitInput_of_initial_and_pushouts
    (D : Type u) [Category.{v} D] [HasInitial D] [HasPushouts D] :
    SourceFiniteColimitInput D where
  finiteColimits := hasFiniteColimits_of_hasInitial_and_pushouts

/-- Named route state for the opposite source finite-limit boundary. -/
structure OppositeSourceFiniteLimitState : Type where
  route : String
  sourceInput : String
  generatedOutput : String
  concreteRemainingInput : String
  constructorCandidate : String
  productSuccessClaimed : Bool

/-- Reproducible state for this audit boundary. -/
def currentOppositeSourceFiniteLimitState : OppositeSourceFiniteLimitState where
  route := "HasFiniteColimits C -> HasFiniteLimits (BoundedComplexCategory C)^op"
  sourceInput := "SourceFiniteColimitInput C"
  generatedOutput :=
    "HasFiniteProducts and HasEqualizers on (BoundedComplexCategory C)^op"
  concreteRemainingInput := "HasFiniteColimits MetrizableLCA"
  constructorCandidate := "hasFiniteColimits_of_hasInitial_and_pushouts"
  productSuccessClaimed := false

theorem currentOppositeSourceFiniteLimitState_not_productSuccess :
    currentOppositeSourceFiniteLimitState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def oppositeSourceFiniteLimitDeclarationNames : List String :=
  ["boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits",
    "boundedComplexOp_hasFiniteProducts_of_sourceFiniteColimits",
    "boundedComplexOp_hasEqualizers_of_sourceFiniteColimits",
    "SourceFiniteColimitInput",
    "boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput",
    "boundedComplexOp_hasFiniteProducts_of_sourceFiniteColimitInput",
    "boundedComplexOp_hasEqualizers_of_sourceFiniteColimitInput",
    "sourceFiniteColimitInput_of_initial_and_pushouts",
    "currentOppositeSourceFiniteLimitState"]

theorem oppositeSourceFiniteLimitDeclarationNames_count :
    oppositeSourceFiniteLimitDeclarationNames.length = 9 := rfl

section Checks

#check boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits
#check boundedComplexOp_hasFiniteProducts_of_sourceFiniteColimits
#check boundedComplexOp_hasEqualizers_of_sourceFiniteColimits
#check SourceFiniteColimitInput
#check boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput
#check boundedComplexOp_hasFiniteProducts_of_sourceFiniteColimitInput
#check boundedComplexOp_hasEqualizers_of_sourceFiniteColimitInput
#check sourceFiniteColimitInput_of_initial_and_pushouts
#check currentOppositeSourceFiniteLimitState
#check currentOppositeSourceFiniteLimitState_not_productSuccess
#check oppositeSourceFiniteLimitDeclarationNames
#check oppositeSourceFiniteLimitDeclarationNames_count
#check Limits.hasFiniteColimits_opposite_iff
#check hasFiniteColimits_of_hasInitial_and_pushouts

end Checks

end OppositeSourceFiniteLimitsW234

end LeanLCAExactChallenge
