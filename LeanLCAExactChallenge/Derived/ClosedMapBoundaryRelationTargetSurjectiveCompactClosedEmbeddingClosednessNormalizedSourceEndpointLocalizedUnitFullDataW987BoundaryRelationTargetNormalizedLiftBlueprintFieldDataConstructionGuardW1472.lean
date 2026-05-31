import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionGuardW1471

/-!
W1472 refines W1471 by constructing the normalized strict-representative lift
blueprint from its raw lift blueprint and normalization fields, then running
the resulting data through the W1471 W987 construction.
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
W1472 replaces W1471's normalized strict-representative lift blueprint by the
raw lift blueprint and the two normalization fields used to construct it.
-/
structure W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472 :
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
  normalizedLiftRawBlueprint :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint
  normalizedLiftObjImage :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (normalizedLiftRawBlueprint.objData
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  normalizedLiftMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (normalizedLiftRawBlueprint.mapData
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImage Y) =
      eqToHom (normalizedLiftObjImage X) ≫ τ
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

/-- W1472 keeps the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1472 builds the W519 provider from its raw closed-embedding field. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding := input.mappedExplicitCokernelClosedEmbedding

/-- W1472 builds the normalized lift blueprint from the raw lift data. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint := input.normalizedLiftRawBlueprint
  obj_image := input.normalizedLiftObjImage
  map_image := input.normalizedLiftMapImage

/-- W1472 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
      input

/-- W1472 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1472 builds the W1471 input after reconstructing the normalized lift blueprint. -/
def w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    W987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputW1471 where
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
  mappedExplicitCokernelClosedEmbedding :=
    input.mappedExplicitCokernelClosedEmbedding
  normalizedLiftBlueprint :=
    normalizedLiftBlueprintOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
      input
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

/-- W1472 builds W945 localized-unit data through W1471. -/
def localizedUnitDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
      input)

/-- W1472 builds W730 boundary/relation data through W1471. -/
def boundaryRelationDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
      input)

/-- W1472 builds W986 target/endpoint data through W1471. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
      input)

/-- W1472 builds W987 full data through W1471. -/
noncomputable def fullDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
      input)

/-- W1472's constructed W718 provider keeps the first component field. -/
theorem w1472GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1472's constructed W718 provider keeps the second component field. -/
theorem w1472GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1472's constructed W718 provider keeps the third component field. -/
theorem w1472GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1472's constructed W973 data keeps the constructed W718 provider. -/
theorem w1472ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input :=
  rfl

/-- W1472's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1472ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input :=
  rfl

/-- W1472's constructed W519 provider keeps the raw closed-embedding field. -/
theorem w1472MappedCokernelClosedEmbeddingProviderKeepsRawField
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).isClosedEmbedding f =
      input.mappedExplicitCokernelClosedEmbedding f :=
  rfl

/-- W1472's normalized lift blueprint keeps the raw lift blueprint. -/
theorem w1472NormalizedLiftBlueprintKeepsRawBlueprint
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).blueprint =
      input.normalizedLiftRawBlueprint :=
  rfl

/-- W1472's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1472NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).obj_image X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1472's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1472NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).map_image τ =
      input.normalizedLiftMapImage τ :=
  rfl

/-- W1472's W1471 input keeps the first W718 component field. -/
theorem w1472W1471InputKeepsGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).globalClosedEmbeddingPi1 =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1472's W1471 input keeps the second W718 component field. -/
theorem w1472W1471InputKeepsGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).globalClosedEmbeddingPi2 =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1472's W1471 input keeps the third W718 component field. -/
theorem w1472W1471InputKeepsGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).globalClosedEmbeddingPi3 =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1472's W1471 input keeps W519 mapped-cokernel data. -/
theorem w1472W1471InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataW1471
        (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input :=
  rfl

/-- W1472's W1471 input keeps the constructed normalized lift blueprint. -/
theorem w1472W1471InputKeepsConstructedNormalizedLiftBlueprint
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).normalizedLiftBlueprint =
      normalizedLiftBlueprintOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input :=
  rfl

/-- W1472's W1471 input keeps target-difference surjectivity. -/
theorem w1472W1471InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1472's W1471 input keeps target-codomain compact no-univ membership. -/
theorem w1472W1471InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1472's W1471 input keeps the reconstructed localized right adjoint. -/
theorem w1472W1471InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    boundedHomotopyLocalizedRightAdjointOfW1471
        (w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1472 input :=
  rfl

/-- W1472's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1472LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1472 input :=
  rfl

/-- W1472's W986 construction keeps the constructed W973 closedness data. -/
theorem w1472TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input :=
  rfl

/-- W1472's constructed W987 provider projects to the constructed W730 data. -/
theorem w1472FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input :=
  rfl

/-- W1472's constructed W987 provider projects to the constructed W986 data. -/
theorem w1472FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        input :=
  rfl

def w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputNamesW1472 :
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
    "normalized lift raw blueprint",
    "normalized lift object-image normalization",
    "normalized lift map-image normalization",
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

theorem w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputNamesW1472_count :
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputNamesW1472.length =
      41 :=
  rfl

def w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionBundledNormalizedLiftInputNamesW1472 :
    List String :=
  ["normalized lift blueprint"]

theorem w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionBundledNormalizedLiftInputNamesW1472_count :
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionBundledNormalizedLiftInputNamesW1472.length =
      1 :=
  rfl

def w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionNormalizedLiftFieldInputNamesW1472 :
    List String :=
  ["normalized lift raw blueprint",
    "normalized lift object-image normalization",
    "normalized lift map-image normalization"]

theorem w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionNormalizedLiftFieldInputNamesW1472_count :
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionNormalizedLiftFieldInputNamesW1472.length =
      3 :=
  rfl

/-- W1472 replaces one normalized lift blueprint by three raw normalized-lift fields. -/
theorem w1472BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionSplitsNormalizedLiftInput :
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionBundledNormalizedLiftInputNamesW1472.length <
      w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionNormalizedLiftFieldInputNamesW1472.length := by
  rw [
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionBundledNormalizedLiftInputNamesW1472_count,
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionNormalizedLiftFieldInputNamesW1472_count]
  decide

/-- W1472 expands the W1471 input count after splitting the normalized lift blueprint. -/
theorem w1472BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionExpandsW1471InputCount :
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputNamesW1471.length <
      w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputNamesW1472.length := by
  rw [
    w987BoundaryRelationTargetMappedCokernelClosedEmbeddingFieldDataConstructionInputNamesW1471_count,
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputNamesW1472_count]
  decide

/-- Current W1472 nonterminal normalized-lift blueprint field construction state. -/
structure W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionStateW1472 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  normalizedLiftBlueprintInputNames : List String
  normalizedLiftBlueprintFieldInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1472 records the normalized-lift blueprint field construction path. -/
def currentW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionStateW1472 :
    W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionStateW1472 where
  seed :=
    "w1472-w987-boundary-relation-target-normalized-lift-blueprint-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472",
      "boundedHomotopyLocalizedRightAdjointOfW1472",
      "w1471InputOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472",
      "localizedUnitDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472",
      "boundaryRelationDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472",
      "fullDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472",
      "w1472GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1472GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1472GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1472ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1472ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1472MappedCokernelClosedEmbeddingProviderKeepsRawField",
      "w1472NormalizedLiftBlueprintKeepsRawBlueprint",
      "w1472NormalizedLiftBlueprintKeepsObjImage",
      "w1472NormalizedLiftBlueprintKeepsMapImage",
      "w1472W1471InputKeepsGlobalClosedEmbeddingPi1",
      "w1472W1471InputKeepsGlobalClosedEmbeddingPi2",
      "w1472W1471InputKeepsGlobalClosedEmbeddingPi3",
      "w1472W1471InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1472W1471InputKeepsConstructedNormalizedLiftBlueprint",
      "w1472W1471InputKeepsTargetDifferenceSurjective",
      "w1472W1471InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1472W1471InputKeepsConstructedLocalizedRightAdjoint",
      "w1472LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1472TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1472FullDataKeepsConstructedBoundaryRelation",
      "w1472FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputNamesW1472_count",
      "w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionBundledNormalizedLiftInputNamesW1472_count",
      "w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionNormalizedLiftFieldInputNamesW1472_count",
      "w1472BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionSplitsNormalizedLiftInput",
      "w1472BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionExpandsW1471InputCount"]
  constructionResult :=
    "proved: W1472 reconstructs the normalized strict-representative lift\
      blueprint from the raw lift blueprint and normalization fields, then\
      feeds that blueprint into W1471"
  projectionResult :=
    "proved: the constructed normalized lift blueprint projects back to\
      its raw blueprint, object-image normalization, and map-image\
      normalization while W1471 preserves localized-unit, boundary, and\
      target/endpoint projections; product success is still not claimed"
  normalizedLiftBlueprintInputNames :=
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionBundledNormalizedLiftInputNamesW1472
  normalizedLiftBlueprintFieldInputNames :=
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionNormalizedLiftFieldInputNamesW1472
  remainingInputs :=
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputNamesW1472
  productSuccessClaimed := false

theorem currentW1472W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionStateW1472.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
