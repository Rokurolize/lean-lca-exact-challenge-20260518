import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionGuardW1470

/-!
W1471 refines W1470 by constructing the W519 mapped explicit cokernel
closed-embedding provider from its raw closed-embedding field, then running the
resulting data through the W1470 W987 construction.
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
W1471 replaces W1470's W519 mapped explicit cokernel closed-embedding
provider by the raw field used to construct that provider.
-/
structure W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471 :
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
  mappedExplicitCokernelClosedEmbedding :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsClosedEmbedding (f : X → Y)
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

/-- W1471 keeps the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1471 builds the W519 provider from its raw closed-embedding field. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding := input.mappedExplicitCokernelClosedEmbedding

/-- W1471 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
      input

/-- W1471 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1471
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1471 builds the W1470 input after reconstructing W519. -/
def w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    W987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputW1470 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    input.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactNoUnivMembershipProvider :=
    input.targetCodomainCompactNoUnivMembershipProvider
  globalClosedEmbeddingPi1 := input.globalClosedEmbeddingPi1
  globalClosedEmbeddingPi2 := input.globalClosedEmbeddingPi2
  globalClosedEmbeddingPi3 := input.globalClosedEmbeddingPi3
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
      input
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

/-- W1471 builds W945 localized-unit data through W1470. -/
def localizedUnitDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
      input)

/-- W1471 builds W730 boundary/relation data through W1470. -/
def boundaryRelationDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
      input)

/-- W1471 builds W986 target/endpoint data through W1470. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
      input)

/-- W1471 builds W987 full data through W1470. -/
noncomputable def fullDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataW1470
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
      input)

/-- W1471's constructed W718 provider keeps the first component field. -/
theorem w1471GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1471's constructed W718 provider keeps the second component field. -/
theorem w1471GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1471's constructed W718 provider keeps the third component field. -/
theorem w1471GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1471's constructed W973 data keeps the constructed W718 provider. -/
theorem w1471ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input :=
  rfl

/-- W1471's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1471ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input :=
  rfl

/-- W1471's constructed W519 provider keeps the raw closed-embedding field. -/
theorem w1471MappedCokernelClosedEmbeddingProviderKeepsRawField
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input).isClosedEmbedding f =
      input.mappedExplicitCokernelClosedEmbedding f :=
  rfl

/-- W1471's W1470 input keeps the first W718 component field. -/
theorem w1471W1470InputKeepsGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input).globalClosedEmbeddingPi1 =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1471's W1470 input keeps the second W718 component field. -/
theorem w1471W1470InputKeepsGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input).globalClosedEmbeddingPi2 =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1471's W1470 input keeps the third W718 component field. -/
theorem w1471W1470InputKeepsGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input).globalClosedEmbeddingPi3 =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1471's W1470 input keeps W519 mapped-cokernel data. -/
theorem w1471W1470InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input).mappedCokernelClosedEmbeddingProvider =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input :=
  rfl

/-- W1471's W1470 input keeps target-difference surjectivity. -/
theorem w1471W1470InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1471's W1470 input keeps target-codomain compact no-univ membership. -/
theorem w1471W1470InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1471's W1470 input keeps the reconstructed localized right adjoint. -/
theorem w1471W1470InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    boundedHomotopyLocalizedRightAdjointOfW1470
        (w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1471 input :=
  rfl

/-- W1471's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1471LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1471 input :=
  rfl

/-- W1471's W986 construction keeps the constructed W973 closedness data. -/
theorem w1471TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input :=
  rfl

/-- W1471's constructed W987 provider projects to the constructed W730 data. -/
theorem w1471FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input :=
  rfl

/-- W1471's constructed W987 provider projects to the constructed W986 data. -/
theorem w1471FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        input :=
  rfl

def w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputNamesW1471 :
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
    "mapped explicit cokernel closed-embedding raw field",
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

theorem w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputNamesW1471_count :
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputNamesW1471.length =
      39 :=
  rfl

def w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionBundledMappedCokernelInputNamesW1471 :
    List String :=
  ["W519 mapped explicit cokernel closed-embedding provider"]

theorem w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionBundledMappedCokernelInputNamesW1471_count :
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionBundledMappedCokernelInputNamesW1471.length =
      1 :=
  rfl

def w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionMappedCokernelFieldInputNamesW1471 :
    List String :=
  ["mapped explicit cokernel closed-embedding raw field"]

theorem w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionMappedCokernelFieldInputNamesW1471_count :
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionMappedCokernelFieldInputNamesW1471.length =
      1 :=
  rfl

/-- W1471 replaces one W519 provider by its raw closed-embedding field. -/
theorem w1471BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionReplacesW519Input :
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionBundledMappedCokernelInputNamesW1471.length =
      w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionMappedCokernelFieldInputNamesW1471.length := by
  rw [
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionBundledMappedCokernelInputNamesW1471_count,
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionMappedCokernelFieldInputNamesW1471_count]

/-- W1471 preserves the W1470 input count after replacing W519 by its raw field. -/
theorem w1471BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionPreservesW1470InputCount :
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputNamesW1470.length =
      w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputNamesW1471.length := by
  rw [
    w987BoundaryRelationTargetSelectedDifferenceClosedEmbeddingComponentFieldDataConstructionInputNamesW1470_count,
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputNamesW1471_count]

/-- Current W1471 nonterminal mapped-cokernel closed-embedding field construction state. -/
structure W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionStateW1471 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  mappedCokernelFieldInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1471 records the W519 field construction path. -/
def currentW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionStateW1471 :
    W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionStateW1471 where
  seed :=
    "w1471-w987-boundary-relation-target-mapped-cokernel-closed-embedding-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471",
      "boundedHomotopyLocalizedRightAdjointOfW1471",
      "w1470InputOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471",
      "localizedUnitDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471",
      "boundaryRelationDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471",
      "fullDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471",
      "w1471GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1471GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1471GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1471ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1471ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1471MappedCokernelClosedEmbeddingProviderKeepsRawField",
      "w1471W1470InputKeepsGlobalClosedEmbeddingPi1",
      "w1471W1470InputKeepsGlobalClosedEmbeddingPi2",
      "w1471W1470InputKeepsGlobalClosedEmbeddingPi3",
      "w1471W1470InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1471W1470InputKeepsTargetDifferenceSurjective",
      "w1471W1470InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1471W1470InputKeepsConstructedLocalizedRightAdjoint",
      "w1471LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1471TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1471FullDataKeepsConstructedBoundaryRelation",
      "w1471FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputNamesW1471_count",
      "w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionBundledMappedCokernelInputNamesW1471_count",
      "w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionMappedCokernelFieldInputNamesW1471_count",
      "w1471BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionReplacesW519Input",
      "w1471BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionPreservesW1470InputCount"]
  constructionResult :=
    "proved: W1471 reconstructs the W519 mapped explicit cokernel\
      closed-embedding provider from its raw field, then feeds that\
      provider into W1470"
  projectionResult :=
    "proved: the constructed W519 provider projects back to its raw field\
      while W1470 preserves localized-unit, boundary, and\
      target/endpoint projections; product success is still not claimed"
  mappedCokernelFieldInputNames :=
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionMappedCokernelFieldInputNamesW1471
  remainingInputs :=
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputNamesW1471
  productSuccessClaimed := false

theorem currentW1471W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionStateW1471.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
