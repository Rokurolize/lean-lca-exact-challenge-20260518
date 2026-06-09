import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldsRoute
import Mathlib.CategoryTheory.Localization.Pi

/-!
Post-`fb234300` frontier probe for the WPP functor-category localization and
source-triangulation boundary.

This file is expected to fail at the `infer_instance` examples. The successful
`#check`s record the exact local constructors that still need concrete inputs.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

#check CategoryTheory.Functor.IsLocalization.pi
#check Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput
#check Dbounded.MetrizableWalkingParallelPairNormalizedFixedTargetInputs
#check Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
#check Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
#check Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
#check Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_fixedTargetData
#check Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetInputs
#check Dbounded.MetrizableWalkingParallelPairStrictPreimageData
#check Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData

example :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput := by
  infer_instance

example :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions := by
  infer_instance

example :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) := by
  infer_instance

example :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      inferInstance
    IsTriangulated (BoundedComplexCategory MetrizableLCA.{0}) := by
  infer_instance

end LeanLCAExactChallenge
