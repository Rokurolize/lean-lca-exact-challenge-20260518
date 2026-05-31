import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionGuardW1472

/-!
W1473 refines W1472 by constructing the raw strict-representative lift
blueprint from its object, map, identity, and composition fields, then running
the resulting data through the W1472 W987 construction.
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
W1473 replaces W1472's raw strict-representative lift blueprint by the
four fields used to construct that blueprint.
-/
structure W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473 :
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
  normalizedLiftObjData :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y
  normalizedLiftMapData :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (normalizedLiftObjData Y) (normalizedLiftObjData Z) τ
  normalizedLiftMapId :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (normalizedLiftMapData (𝟙 Y)).natTrans =
        𝟙 (normalizedLiftObjData Y).diagram
  normalizedLiftMapComp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (normalizedLiftMapData (τ ≫ σ)).natTrans =
        (normalizedLiftMapData τ).natTrans ≫
          (normalizedLiftMapData σ).natTrans
  normalizedLiftObjImage :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (normalizedLiftObjData
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  normalizedLiftMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (normalizedLiftMapData
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

/-- W1473 keeps the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1473 builds the W519 provider from its raw closed-embedding field. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding := input.mappedExplicitCokernelClosedEmbedding

/-- W1473 builds the raw lift blueprint from its functorial fields. -/
def normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData := input.normalizedLiftObjData
  mapData := input.normalizedLiftMapData
  map_id := input.normalizedLiftMapId
  map_comp := input.normalizedLiftMapComp

/-- W1473 builds the normalized lift blueprint from the raw lift fields. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
      input
  obj_image := input.normalizedLiftObjImage
  map_image := input.normalizedLiftMapImage

/-- W1473 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
      input

/-- W1473 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1473 builds the W1472 input after reconstructing the normalized lift blueprint. -/
def w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    W987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputW1472 where
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
  normalizedLiftRawBlueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
      input
  normalizedLiftObjImage := input.normalizedLiftObjImage
  normalizedLiftMapImage := input.normalizedLiftMapImage
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

/-- W1473 builds W945 localized-unit data through W1472. -/
def localizedUnitDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
      input)

/-- W1473 builds W730 boundary/relation data through W1472. -/
def boundaryRelationDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
      input)

/-- W1473 builds W986 target/endpoint data through W1472. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
      input)

/-- W1473 builds W987 full data through W1472. -/
noncomputable def fullDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
      input)

/-- W1473's constructed W718 provider keeps the first component field. -/
theorem w1473GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1473's constructed W718 provider keeps the second component field. -/
theorem w1473GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1473's constructed W718 provider keeps the third component field. -/
theorem w1473GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1473's constructed W973 data keeps the constructed W718 provider. -/
theorem w1473ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input :=
  rfl

/-- W1473's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1473ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input :=
  rfl

/-- W1473's constructed W519 provider keeps the raw closed-embedding field. -/
theorem w1473MappedCokernelClosedEmbeddingProviderKeepsRawField
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).isClosedEmbedding f =
      input.mappedExplicitCokernelClosedEmbedding f :=
  rfl

/-- W1473's raw lift blueprint keeps the object-data field. -/
theorem w1473NormalizedLiftRawBlueprintKeepsObjData
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).objData =
      input.normalizedLiftObjData :=
  rfl

/-- W1473's raw lift blueprint keeps the map-data field. -/
theorem w1473NormalizedLiftRawBlueprintKeepsMapData
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).mapData τ =
      input.normalizedLiftMapData τ :=
  rfl

/-- W1473's raw lift blueprint keeps the identity law. -/
theorem w1473NormalizedLiftRawBlueprintKeepsMapId
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).map_id Y =
      input.normalizedLiftMapId Y :=
  rfl

/-- W1473's raw lift blueprint keeps the composition law. -/
theorem w1473NormalizedLiftRawBlueprintKeepsMapComp
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).map_comp τ σ =
      input.normalizedLiftMapComp τ σ :=
  rfl

/-- W1473's normalized lift blueprint keeps the constructed raw lift blueprint. -/
theorem w1473NormalizedLiftBlueprintKeepsConstructedRawBlueprint
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).blueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input :=
  rfl

/-- W1473's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1473NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).obj_image X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1473's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1473NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).map_image τ =
      input.normalizedLiftMapImage τ :=
  rfl

/-- W1473's W1472 input keeps the first W718 component field. -/
theorem w1473W1472InputKeepsGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).globalClosedEmbeddingPi1 =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1473's W1472 input keeps the second W718 component field. -/
theorem w1473W1472InputKeepsGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).globalClosedEmbeddingPi2 =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1473's W1472 input keeps the third W718 component field. -/
theorem w1473W1472InputKeepsGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).globalClosedEmbeddingPi3 =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1473's W1472 input keeps W519 mapped-cokernel data. -/
theorem w1473W1472InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataW1472
        (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input :=
  rfl

/-- W1473's W1472 input keeps the constructed raw lift blueprint. -/
theorem w1473W1472InputKeepsConstructedRawLiftBlueprint
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).normalizedLiftRawBlueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input :=
  rfl

/-- W1473's W1472 input keeps the object-image normalization field. -/
theorem w1473W1472InputKeepsNormalizedLiftObjImage
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).normalizedLiftObjImage X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1473's W1472 input keeps the map-image normalization field. -/
theorem w1473W1472InputKeepsNormalizedLiftMapImage
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).normalizedLiftMapImage τ =
      input.normalizedLiftMapImage τ :=
  rfl

/-- W1473's W1472 input keeps target-difference surjectivity. -/
theorem w1473W1472InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1473's W1472 input keeps target-codomain compact no-univ membership. -/
theorem w1473W1472InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1473's W1472 input keeps the reconstructed localized right adjoint. -/
theorem w1473W1472InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    boundedHomotopyLocalizedRightAdjointOfW1472
        (w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1473 input :=
  rfl

/-- W1473's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1473LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1473 input :=
  rfl

/-- W1473's W986 construction keeps the constructed W973 closedness data. -/
theorem w1473TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input :=
  rfl

/-- W1473's constructed W987 provider projects to the constructed W730 data. -/
theorem w1473FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input :=
  rfl

/-- W1473's constructed W987 provider projects to the constructed W986 data. -/
theorem w1473FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        input :=
  rfl

def w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputNamesW1473 :
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
    "normalized lift object strict-preimage data family",
    "normalized lift map strict-preimage data family",
    "normalized lift map identity law",
    "normalized lift map composition law",
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

theorem w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputNamesW1473_count :
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputNamesW1473.length =
      44 :=
  rfl

def w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionBundledRawLiftInputNamesW1473 :
    List String :=
  ["normalized lift raw blueprint"]

theorem w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionBundledRawLiftInputNamesW1473_count :
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionBundledRawLiftInputNamesW1473.length =
      1 :=
  rfl

def w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionRawLiftFieldInputNamesW1473 :
    List String :=
  ["normalized lift object strict-preimage data family",
    "normalized lift map strict-preimage data family",
    "normalized lift map identity law",
    "normalized lift map composition law"]

theorem w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionRawLiftFieldInputNamesW1473_count :
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionRawLiftFieldInputNamesW1473.length =
      4 :=
  rfl

/-- W1473 replaces one raw lift blueprint by its four functorial fields. -/
theorem w1473BoundaryRelationTargetLiftBlueprintFieldDataConstructionSplitsRawLiftInput :
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionBundledRawLiftInputNamesW1473.length <
      w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionRawLiftFieldInputNamesW1473.length := by
  rw [
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionBundledRawLiftInputNamesW1473_count,
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionRawLiftFieldInputNamesW1473_count]
  decide

/-- W1473 expands the W1472 input count after splitting the raw lift blueprint. -/
theorem w1473BoundaryRelationTargetLiftBlueprintFieldDataConstructionExpandsW1472InputCount :
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputNamesW1472.length <
      w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputNamesW1473.length := by
  rw [
    w987BoundaryRelationTargetNormalizedLiftBlueprintFieldDataConstructionInputNamesW1472_count,
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputNamesW1473_count]
  decide

/-- Current W1473 nonterminal raw lift-blueprint field construction state. -/
structure W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionStateW1473 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  rawLiftBlueprintInputNames : List String
  rawLiftBlueprintFieldInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1473 records the raw lift-blueprint field construction path. -/
def currentW987BoundaryRelationTargetLiftBlueprintFieldDataConstructionStateW1473 :
    W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionStateW1473 where
  seed :=
    "w1473-w987-boundary-relation-target-lift-blueprint-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473",
      "normalizedLiftRawBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473",
      "normalizedLiftBlueprintOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473",
      "boundedHomotopyLocalizedRightAdjointOfW1473",
      "w1472InputOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473",
      "localizedUnitDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473",
      "boundaryRelationDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473",
      "fullDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473",
      "w1473GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1473GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1473GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1473ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1473ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1473MappedCokernelClosedEmbeddingProviderKeepsRawField",
      "w1473NormalizedLiftRawBlueprintKeepsObjData",
      "w1473NormalizedLiftRawBlueprintKeepsMapData",
      "w1473NormalizedLiftRawBlueprintKeepsMapId",
      "w1473NormalizedLiftRawBlueprintKeepsMapComp",
      "w1473NormalizedLiftBlueprintKeepsConstructedRawBlueprint",
      "w1473NormalizedLiftBlueprintKeepsObjImage",
      "w1473NormalizedLiftBlueprintKeepsMapImage",
      "w1473W1472InputKeepsGlobalClosedEmbeddingPi1",
      "w1473W1472InputKeepsGlobalClosedEmbeddingPi2",
      "w1473W1472InputKeepsGlobalClosedEmbeddingPi3",
      "w1473W1472InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1473W1472InputKeepsConstructedRawLiftBlueprint",
      "w1473W1472InputKeepsNormalizedLiftObjImage",
      "w1473W1472InputKeepsNormalizedLiftMapImage",
      "w1473W1472InputKeepsTargetDifferenceSurjective",
      "w1473W1472InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1473W1472InputKeepsConstructedLocalizedRightAdjoint",
      "w1473LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1473TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1473FullDataKeepsConstructedBoundaryRelation",
      "w1473FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputNamesW1473_count",
      "w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionBundledRawLiftInputNamesW1473_count",
      "w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionRawLiftFieldInputNamesW1473_count",
      "w1473BoundaryRelationTargetLiftBlueprintFieldDataConstructionSplitsRawLiftInput",
      "w1473BoundaryRelationTargetLiftBlueprintFieldDataConstructionExpandsW1472InputCount"]
  constructionResult :=
    "proved: W1473 reconstructs the raw strict-representative lift blueprint\
      from object, map, identity, and composition fields, then feeds that\
      blueprint into W1472"
  projectionResult :=
    "proved: the constructed raw lift blueprint projects back to object,\
      map, identity, and composition fields while W1472 preserves\
      localized-unit, boundary, and target/endpoint projections; product\
      success is still not claimed"
  rawLiftBlueprintInputNames :=
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionBundledRawLiftInputNamesW1473
  rawLiftBlueprintFieldInputNames :=
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionRawLiftFieldInputNamesW1473
  remainingInputs :=
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputNamesW1473
  productSuccessClaimed := false

theorem currentW1473W987BoundaryRelationTargetLiftBlueprintFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetLiftBlueprintFieldDataConstructionStateW1473.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
