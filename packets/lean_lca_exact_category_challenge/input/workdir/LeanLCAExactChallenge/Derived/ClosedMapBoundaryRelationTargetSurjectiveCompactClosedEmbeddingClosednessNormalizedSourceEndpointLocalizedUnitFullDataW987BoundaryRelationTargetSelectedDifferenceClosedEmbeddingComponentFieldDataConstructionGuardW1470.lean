import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionGuardW1469

/-!
W1470 refines W1469 by constructing the W718 selected-difference
closed-embedding component provider from its three W714 diagram fields, then
running the resulting data through the W1469 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/--
W1470 replaces W1469's W718 selected-difference closed-embedding component
provider by the three diagram fields used to construct that provider.
-/
structure W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470 :
    Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationPullbackProvider :
    ClosedNatTransOrdinaryRelationPullbackProviderW712
  targetRelationLiftsProvider :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
  targetDifferenceSurjectiveForTargetProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y
  targetCodomainCompactNoUnivMembershipProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y
  globalClosedEmbeddingPi1 :
    SelectedDifferenceClosedEmbeddingPi1DiagramFieldW714
  globalClosedEmbeddingPi2 :
    SelectedDifferenceClosedEmbeddingPi2DiagramFieldW714
  globalClosedEmbeddingPi3 :
    SelectedDifferenceClosedEmbeddingPi3DiagramFieldW714
  mappedCokernelClosedEmbeddingProvider :
    MappedExplicitCokernelClosedEmbeddingProviderW519
  normalizedLiftBlueprint :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
  targetFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  localizationModelFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)
  sourcePretriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    Pretriangulated (BoundedComplexCategory MetrizableLCA.{0})
  sourceTriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    IsTriangulated (BoundedComplexCategory MetrizableLCA.{0})
  triangleCompletion :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointCokernelTop :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.cokernelSubgroup (K.sc i).g = ⊤
  endpointKernelEquality :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₂ : (K.sc i).X₂),
        (K.sc i).g x₂ = 0 ↔
          ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂
  boundedHomotopyLocalizedRightAdjointFields :
    LocalizedRightAdjointFunctorFieldsW1467
  boundedHomotopyLocalizedAdjunctionUnitApp :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      X ⟶
        (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
          localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields).obj X
  boundedHomotopyLocalizedAdjunctionUnitNaturality :
    ∀ {X Y : BoundedComplexCategory MetrizableLCA.{0}} (f : X ⟶ Y),
      f ≫ boundedHomotopyLocalizedAdjunctionUnitApp Y =
        boundedHomotopyLocalizedAdjunctionUnitApp X ≫
          (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
            localizedRightAdjointOfW1467
              boundedHomotopyLocalizedRightAdjointFields).map f
  boundedHomotopyLocalizedAdjunctionCounitApp :
    ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
      ((localizedRightAdjointOfW1467
          boundedHomotopyLocalizedRightAdjointFields) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).obj Y ⟶
        Y
  boundedHomotopyLocalizedAdjunctionCounitNaturality :
    ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y),
      ((localizedRightAdjointOfW1467
          boundedHomotopyLocalizedRightAdjointFields) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).map f ≫
          boundedHomotopyLocalizedAdjunctionCounitApp Y =
        boundedHomotopyLocalizedAdjunctionCounitApp X ≫ f
  boundedHomotopyLocalizedAdjunctionLeftTriangleApp :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (localizedAdjunctionLeftTriangleNatTransOfW1467
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          boundedHomotopyLocalizedAdjunctionUnitApp
          boundedHomotopyLocalizedAdjunctionUnitNaturality
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality).app X =
        (NatTrans.id
          (𝟭 (BoundedComplexCategory MetrizableLCA.{0}) ⋙
            boundedHomotopyLocalizedVerdierFunctorW1461)).app X
  boundedHomotopyLocalizedAdjunctionRightTriangleApp :
    ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
      (localizedAdjunctionRightTriangleNatTransOfW1467
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          boundedHomotopyLocalizedAdjunctionUnitApp
          boundedHomotopyLocalizedAdjunctionUnitNaturality
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality).app Y =
        (NatTrans.id
          ((localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields) ⋙
            𝟭 (BoundedComplexCategory MetrizableLCA.{0}))).app Y
  unitMappingConeModel :
    UnitMappingConeModelW962
  unitMappingConeClosedEmbedding :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsClosedEmbedding (((unitMappingConeModel X).as.sc i).f :
        ((unitMappingConeModel X).as.sc i).X₁ →
          ((unitMappingConeModel X).as.sc i).X₂)
  unitMappingConeOpenMap :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsOpenMap (((unitMappingConeModel X).as.sc i).g :
        ((unitMappingConeModel X).as.sc i).X₂ →
          ((unitMappingConeModel X).as.sc i).X₃)
  unitMappingConeCokernelTop :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.cokernelSubgroup (((unitMappingConeModel X).as.sc i).g) =
        ⊤
  unitMappingConeKernelEquality :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((unitMappingConeModel X).as.sc i).X₂),
        ((unitMappingConeModel X).as.sc i).g x₂ = 0 ↔
          ∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
            ((unitMappingConeModel X).as.sc i).f x₁ = x₂
  unitMappingConeIsoHom :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoSourceW1464
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfW1467
              boundedHomotopyLocalizedRightAdjointFields)
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X ⟶
        unitMappingConeModel X
  unitMappingConeIsoInv :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeModel X ⟶
        unitMappingConeIsoSourceW1464
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfW1467
              boundedHomotopyLocalizedRightAdjointFields)
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X
  unitMappingConeIsoHomInvId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoHom X ≫ unitMappingConeIsoInv X =
        𝟙 (unitMappingConeIsoSourceW1464
          (localizedRightAdjointOfW1467
            boundedHomotopyLocalizedRightAdjointFields)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfW1467
              boundedHomotopyLocalizedRightAdjointFields)
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X)
  unitMappingConeIsoInvHomId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoInv X ≫ unitMappingConeIsoHom X =
        𝟙 (unitMappingConeModel X)

/-- W1470 builds W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1470 builds W973 closed-embedding closedness data from component fields. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
      input
  mappedCokernelClosedEmbeddingProvider :=
    input.mappedCokernelClosedEmbeddingProvider

/-- W1470 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1470
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1470 builds the W1469 input after reconstructing W718. -/
def w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    input.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactNoUnivMembershipProvider :=
    input.targetCodomainCompactNoUnivMembershipProvider
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
      input
  mappedCokernelClosedEmbeddingProvider :=
    input.mappedCokernelClosedEmbeddingProvider
  normalizedLiftBlueprint := input.normalizedLiftBlueprint
  targetFixedTargetUniq := input.targetFixedTargetUniq
  localizationModelFixedTargetUniq := input.localizationModelFixedTargetUniq
  sourcePretriangulated := input.sourcePretriangulated
  sourceTriangulated := input.sourceTriangulated
  triangleCompletion := input.triangleCompletion
  endpointClosedEmbedding := input.endpointClosedEmbedding
  endpointOpenMap := input.endpointOpenMap
  endpointCokernelTop := input.endpointCokernelTop
  endpointKernelEquality := input.endpointKernelEquality
  boundedHomotopyLocalizedRightAdjointFields :=
    input.boundedHomotopyLocalizedRightAdjointFields
  boundedHomotopyLocalizedAdjunctionUnitApp :=
    input.boundedHomotopyLocalizedAdjunctionUnitApp
  boundedHomotopyLocalizedAdjunctionUnitNaturality :=
    input.boundedHomotopyLocalizedAdjunctionUnitNaturality
  boundedHomotopyLocalizedAdjunctionCounitApp :=
    input.boundedHomotopyLocalizedAdjunctionCounitApp
  boundedHomotopyLocalizedAdjunctionCounitNaturality :=
    input.boundedHomotopyLocalizedAdjunctionCounitNaturality
  boundedHomotopyLocalizedAdjunctionLeftTriangleApp :=
    input.boundedHomotopyLocalizedAdjunctionLeftTriangleApp
  boundedHomotopyLocalizedAdjunctionRightTriangleApp :=
    input.boundedHomotopyLocalizedAdjunctionRightTriangleApp
  unitMappingConeModel := input.unitMappingConeModel
  unitMappingConeClosedEmbedding := input.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := input.unitMappingConeOpenMap
  unitMappingConeCokernelTop := input.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := input.unitMappingConeKernelEquality
  unitMappingConeIsoHom := input.unitMappingConeIsoHom
  unitMappingConeIsoInv := input.unitMappingConeIsoInv
  unitMappingConeIsoHomInvId := input.unitMappingConeIsoHomInvId
  unitMappingConeIsoInvHomId := input.unitMappingConeIsoInvHomId

/-- W1470 builds W945 localized-unit data through W1469. -/
def localizedUnitDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
      input)

/-- W1470 builds W730 boundary/relation data through W1469. -/
def boundaryRelationDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
      input)

/-- W1470 builds W986 target/endpoint data through W1469. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
      input)

/-- W1470 builds W987 full data through W1469. -/
noncomputable def fullDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
      input)

/-- W1470's constructed W718 provider keeps the first component field. -/
theorem w1470GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1470's constructed W718 provider keeps the second component field. -/
theorem w1470GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1470's constructed W718 provider keeps the third component field. -/
theorem w1470GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1470's constructed W973 data keeps the constructed W718 provider. -/
theorem w1470ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
        input :=
  rfl

/-- W1470's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1470ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
          input) =
      input.mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1470's W1469 input keeps the constructed W718 provider. -/
theorem w1470W1469InputKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    (w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
        input).globalClosedEmbeddingComponents =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
        input :=
  rfl

/-- W1470's W1469 input keeps W519 mapped-cokernel data. -/
theorem w1470W1469InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    (w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
        input).mappedCokernelClosedEmbeddingProvider =
      input.mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1470's W1469 input keeps target-difference surjectivity. -/
theorem w1470W1469InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    (w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1470's W1469 input keeps target-codomain compact no-univ membership. -/
theorem w1470W1469InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    (w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1470's W1469 input keeps the reconstructed localized right adjoint. -/
theorem w1470W1469InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    boundedHomotopyLocalizedRightAdjointOfW1469
        (w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1470 input :=
  rfl

/-- W1470's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1470LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1470 input :=
  rfl

/-- W1470's W986 construction keeps the constructed W973 closedness data. -/
theorem w1470TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
        input :=
  rfl

/-- W1470's constructed W987 provider projects to the constructed W730 data. -/
theorem w1470FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
        input :=
  rfl

/-- W1470's constructed W987 provider projects to the constructed W986 data. -/
theorem w1470FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
        input :=
  rfl

def w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputNamesW1470 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "target-difference surjectivity primitive family",
    "target-codomain compact no-univ membership primitive family",
    "first selected-difference closed-embedding diagram component field",
    "second selected-difference closed-embedding diagram component field",
    "third selected-difference closed-embedding diagram component field",
    "W519 mapped explicit cokernel closed-embedding provider",
    "normalized lift blueprint",
    "target fixed-target uniqueness",
    "localization-model fixed-target uniqueness",
    "source pretriangulated structure",
    "source triangulated structure",
    "source triangle-completion input",
    "endpoint closed-embedding family",
    "endpoint open-map family",
    "endpoint cokernel-top family",
    "endpoint kernel-equality family",
    "bounded homotopy localized right-adjoint object map",
    "bounded homotopy localized right-adjoint morphism map",
    "bounded homotopy localized right-adjoint identity law",
    "bounded homotopy localized right-adjoint composition law",
    "localized adjunction unit component family",
    "localized adjunction unit naturality proof",
    "localized adjunction counit component family",
    "localized adjunction counit naturality proof",
    "localized adjunction left component identity family",
    "localized adjunction right component identity family",
    "unit mapping-cone model",
    "unit mapping-cone closed-embedding family",
    "unit mapping-cone open-map family",
    "unit mapping-cone cokernel-top family",
    "unit mapping-cone kernel-equality family",
    "unit mapping-cone isomorphism hom",
    "unit mapping-cone isomorphism inv",
    "unit mapping-cone isomorphism hom-inv identity",
    "unit mapping-cone isomorphism inv-hom identity"]

theorem w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputNamesW1470_count :
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputNamesW1470.length =
      39 :=
  rfl

def w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionBundledComponentInputNamesW1470 :
    List String :=
  ["W718 selected-difference closed-embedding diagram component provider"]

theorem w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionBundledComponentInputNamesW1470_count :
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionBundledComponentInputNamesW1470.length =
      1 :=
  rfl

def w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionComponentFieldInputNamesW1470 :
    List String :=
  ["first selected-difference closed-embedding diagram component field",
    "second selected-difference closed-embedding diagram component field",
    "third selected-difference closed-embedding diagram component field"]

theorem w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionComponentFieldInputNamesW1470_count :
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionComponentFieldInputNamesW1470.length =
      3 :=
  rfl

/-- W1470 replaces one W718 provider by three component fields. -/
theorem w1470BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionSplitsW718Input :
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionBundledComponentInputNamesW1470.length <
      w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionComponentFieldInputNamesW1470.length := by
  rw [
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionBundledComponentInputNamesW1470_count,
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionComponentFieldInputNamesW1470_count]
  decide

/-- W1470 expands the W1469 input count by decomposing W718 component data. -/
theorem w1470BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionExpandsW1469InputCount :
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputNamesW1469.length <
      w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputNamesW1470.length := by
  rw [
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputNamesW1469_count,
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputNamesW1470_count]
  decide

/-- Current W1470 nonterminal component-field construction state. -/
structure W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionStateW1470 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  componentFieldInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1470 records the W718 component-field construction path. -/
def currentW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionStateW1470 :
    W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionStateW1470 where
  seed :=
    "w1470-w987-boundary-relation-target-selected-difference-closed-embedding-component-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470",
      "boundedHomotopyLocalizedRightAdjointOfW1470",
      "w1469InputOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470",
      "localizedUnitDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470",
      "boundaryRelationDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470",
      "fullDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470",
      "w1470GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1470GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1470GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1470ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1470ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1470W1469InputKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1470W1469InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1470W1469InputKeepsTargetDifferenceSurjective",
      "w1470W1469InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1470W1469InputKeepsConstructedLocalizedRightAdjoint",
      "w1470LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1470TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1470FullDataKeepsConstructedBoundaryRelation",
      "w1470FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputNamesW1470_count",
      "w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionBundledComponentInputNamesW1470_count",
      "w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionComponentFieldInputNamesW1470_count",
      "w1470BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionSplitsW718Input",
      "w1470BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionExpandsW1469InputCount"]
  constructionResult :=
    "proved: W1470 reconstructs the W718 selected-difference closed-embedding\
      component provider from three W714 diagram fields, then feeds that\
      provider into W1469"
  projectionResult :=
    "proved: the constructed W718 provider projects back to its three component\
      fields while W1469 preserves localized-unit, boundary, and\
      target/endpoint projections; product success is still not claimed"
  componentFieldInputNames :=
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionComponentFieldInputNamesW1470
  remainingInputs :=
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputNamesW1470
  productSuccessClaimed := false

theorem currentW1470W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionStateW1470.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
