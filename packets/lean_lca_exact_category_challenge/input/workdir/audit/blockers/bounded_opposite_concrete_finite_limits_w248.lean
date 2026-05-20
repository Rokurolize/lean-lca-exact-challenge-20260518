import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Opposites

/-!
W248 audit: concrete finite-limit input for the bounded opposite source.

This specializes the source-side finite-colimit route to `MetrizableLCA`, using
the cokernel-based `HasFiniteColimits` instance already implemented in the
parent target.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace BoundedOppositeConcreteFiniteLimitsW248

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Local wrapper matching the finite-colimit source input isolated by W234. -/
structure SourceFiniteColimitInput : Prop where
  finiteColimits : HasFiniteColimits C

/-- Finite colimits in the source category give finite limits on bounded complexes' opposite. -/
theorem boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits [HasFiniteColimits C] :
    HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits (BoundedComplexCategory C) := inferInstance
  exact Limits.hasFiniteColimits_opposite_iff.mp inferInstance

/-- Wrapped finite-limit consumer for callers carrying the source input as one field. -/
theorem boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput
    (h : SourceFiniteColimitInput C) :
    HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits C := h.finiteColimits
  exact boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits C

/-- The source finite-colimit input is inhabited for concrete `MetrizableLCA`. -/
theorem metrizableLCA_sourceFiniteColimitInput :
    SourceFiniteColimitInput MetrizableLCA.{u} where
  finiteColimits := inferInstance

/-- Concrete specialization: bounded complexes over `MetrizableLCA` have finite limits on the opposite. -/
theorem metrizableLCA_boundedComplexOp_hasFiniteLimits :
    HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
  boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput MetrizableLCA
    metrizableLCA_sourceFiniteColimitInput

/-- Concrete specialization: finite products on the bounded-complex opposite source. -/
theorem metrizableLCA_boundedComplexOp_hasFiniteProducts :
    HasFiniteProducts (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ := by
  haveI : HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
    metrizableLCA_boundedComplexOp_hasFiniteLimits
  infer_instance

/-- Concrete specialization: equalizers on the bounded-complex opposite source. -/
theorem metrizableLCA_boundedComplexOp_hasEqualizers :
    HasEqualizers (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ := by
  haveI : HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
    metrizableLCA_boundedComplexOp_hasFiniteLimits
  infer_instance

def boundedOppositeConcreteFiniteLimitDeclarationNames : List String :=
  ["SourceFiniteColimitInput",
    "boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits",
    "boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput",
    "metrizableLCA_sourceFiniteColimitInput",
    "metrizableLCA_boundedComplexOp_hasFiniteLimits",
    "metrizableLCA_boundedComplexOp_hasFiniteProducts",
    "metrizableLCA_boundedComplexOp_hasEqualizers"]

theorem boundedOppositeConcreteFiniteLimitDeclarationNames_count :
    boundedOppositeConcreteFiniteLimitDeclarationNames.length = 7 := rfl

section Checks

#check MetrizableLCA.instHasFiniteColimits
#check boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits
#check boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput
#check metrizableLCA_sourceFiniteColimitInput
#check metrizableLCA_boundedComplexOp_hasFiniteLimits
#check metrizableLCA_boundedComplexOp_hasFiniteProducts
#check metrizableLCA_boundedComplexOp_hasEqualizers
#check boundedOppositeConcreteFiniteLimitDeclarationNames_count
#check Limits.hasFiniteColimits_opposite_iff

end Checks

end BoundedOppositeConcreteFiniteLimitsW248

end LeanLCAExactChallenge
