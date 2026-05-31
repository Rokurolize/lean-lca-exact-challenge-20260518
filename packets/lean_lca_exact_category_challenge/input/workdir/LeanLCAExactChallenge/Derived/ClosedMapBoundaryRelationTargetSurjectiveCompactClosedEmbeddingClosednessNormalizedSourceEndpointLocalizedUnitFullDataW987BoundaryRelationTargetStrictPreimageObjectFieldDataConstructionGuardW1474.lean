import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetLiftBlueprintFieldDataConstructionGuardW1473

/-!
W1474 refines W1473 by constructing the strict-preimage object-data family
from its object, isomorphism, source-map, and factorization fields, then running
the resulting data through the W1473 W987 construction.
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

/-- W1474 assembles one strict-preimage object datum from its constructor fields. -/
def normalizedLiftObjDataOfFieldsW1474
    (zeroSrc :
      ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        BoundedComplexCategory MetrizableLCA.{0})
    (oneSrc :
      ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        BoundedComplexCategory MetrizableLCA.{0})
    (zeroIso :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        (Dbounded.localization MetrizableLCA.{0}).obj (zeroSrc Y) ≅
          Y.obj WalkingParallelPair.zero)
    (oneIso :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        (Dbounded.localization MetrizableLCA.{0}).obj (oneSrc Y) ≅
          Y.obj WalkingParallelPair.one)
    (leftSrc :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        zeroSrc Y ⟶ oneSrc Y)
    (rightSrc :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        zeroSrc Y ⟶ oneSrc Y)
    (leftFac :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        (Dbounded.localization MetrizableLCA.{0}).map (leftSrc Y) =
          (zeroIso Y).hom ≫
            Y.map WalkingParallelPairHom.left ≫
              (oneIso Y).inv)
    (rightFac :
      ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
        (Dbounded.localization MetrizableLCA.{0}).map (rightSrc Y) =
          (zeroIso Y).hom ≫
            Y.map WalkingParallelPairHom.right ≫
              (oneIso Y).inv)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y where
  zeroSrc := zeroSrc Y
  oneSrc := oneSrc Y
  zeroIso := zeroIso Y
  oneIso := oneIso Y
  leftSrc := leftSrc Y
  rightSrc := rightSrc Y
  left_fac := leftFac Y
  right_fac := rightFac Y

/--
W1474 replaces W1473's bundled strict-preimage object-data family by the
eight fields used to construct that family.
-/
structure W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474 :
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
  normalizedLiftZeroSrc :
    ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      BoundedComplexCategory MetrizableLCA.{0}
  normalizedLiftOneSrc :
    ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      BoundedComplexCategory MetrizableLCA.{0}
  normalizedLiftZeroIso :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).obj (normalizedLiftZeroSrc Y) ≅
        Y.obj WalkingParallelPair.zero
  normalizedLiftOneIso :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).obj (normalizedLiftOneSrc Y) ≅
        Y.obj WalkingParallelPair.one
  normalizedLiftLeftSrc :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      normalizedLiftZeroSrc Y ⟶ normalizedLiftOneSrc Y
  normalizedLiftRightSrc :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      normalizedLiftZeroSrc Y ⟶ normalizedLiftOneSrc Y
  normalizedLiftLeftFac :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).map
          (normalizedLiftLeftSrc Y) =
        (normalizedLiftZeroIso Y).hom ≫
          Y.map WalkingParallelPairHom.left ≫
            (normalizedLiftOneIso Y).inv
  normalizedLiftRightFac :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).map
          (normalizedLiftRightSrc Y) =
        (normalizedLiftZeroIso Y).hom ≫
          Y.map WalkingParallelPairHom.right ≫
            (normalizedLiftOneIso Y).inv
  normalizedLiftMapData :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (normalizedLiftObjDataOfFieldsW1474 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac Y)
        (normalizedLiftObjDataOfFieldsW1474 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac Z)
        τ
  normalizedLiftMapId :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (normalizedLiftMapData (𝟙 Y)).natTrans =
        𝟙 (normalizedLiftObjDataOfFieldsW1474 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac Y).diagram
  normalizedLiftMapComp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (normalizedLiftMapData (τ ≫ σ)).natTrans =
        (normalizedLiftMapData τ).natTrans ≫
          (normalizedLiftMapData σ).natTrans
  normalizedLiftObjImage :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (normalizedLiftObjDataOfFieldsW1474 normalizedLiftZeroSrc
        normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
        normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
        normalizedLiftRightFac
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

/-- W1474 keeps the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1474 builds the W519 provider from its raw closed-embedding field. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding := input.mappedExplicitCokernelClosedEmbedding

/-- W1474 builds the strict-preimage object-data family from its fields. -/
def normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y :=
  fun Y =>
    normalizedLiftObjDataOfFieldsW1474 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac Y

/-- W1474 builds the raw lift blueprint from its object and functorial fields. -/
def normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData :=
    normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
      input
  mapData := input.normalizedLiftMapData
  map_id := input.normalizedLiftMapId
  map_comp := input.normalizedLiftMapComp

/-- W1474 builds the normalized lift blueprint from the raw lift fields. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
      input
  obj_image := input.normalizedLiftObjImage
  map_image := input.normalizedLiftMapImage

/-- W1474 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
      input

/-- W1474 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1474 builds the W1473 input after reconstructing the object-data family. -/
def w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    W987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputW1473 where
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
  normalizedLiftObjData :=
    normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
      input
  normalizedLiftMapData := input.normalizedLiftMapData
  normalizedLiftMapId := input.normalizedLiftMapId
  normalizedLiftMapComp := input.normalizedLiftMapComp
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

/-- W1474 builds W945 localized-unit data through W1473. -/
def localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
      input)

/-- W1474 builds W730 boundary/relation data through W1473. -/
def boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
      input)

/-- W1474 builds W986 target/endpoint data through W1473. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
      input)

/-- W1474 builds W987 full data through W1473. -/
noncomputable def fullDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
      input)

/-- W1474's constructed W718 provider keeps the first component field. -/
theorem w1474GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1474's constructed W718 provider keeps the second component field. -/
theorem w1474GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1474's constructed W718 provider keeps the third component field. -/
theorem w1474GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1474's constructed W973 data keeps the constructed W718 provider. -/
theorem w1474ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input :=
  rfl

/-- W1474's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1474ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input :=
  rfl

/-- W1474's constructed W519 provider keeps the raw closed-embedding field. -/
theorem w1474MappedCokernelClosedEmbeddingProviderKeepsRawField
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).isClosedEmbedding f =
      input.mappedExplicitCokernelClosedEmbedding f :=
  rfl

/-- W1474's object-data family keeps the zero object field. -/
theorem w1474NormalizedLiftObjDataKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input Y).zeroSrc =
      input.normalizedLiftZeroSrc Y :=
  rfl

/-- W1474's object-data family keeps the one object field. -/
theorem w1474NormalizedLiftObjDataKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input Y).oneSrc =
      input.normalizedLiftOneSrc Y :=
  rfl

/-- W1474's object-data family keeps the zero comparison isomorphism. -/
theorem w1474NormalizedLiftObjDataKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input Y).zeroIso =
      input.normalizedLiftZeroIso Y :=
  rfl

/-- W1474's object-data family keeps the one comparison isomorphism. -/
theorem w1474NormalizedLiftObjDataKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input Y).oneIso =
      input.normalizedLiftOneIso Y :=
  rfl

/-- W1474's object-data family keeps the left source map. -/
theorem w1474NormalizedLiftObjDataKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input Y).leftSrc =
      input.normalizedLiftLeftSrc Y :=
  rfl

/-- W1474's object-data family keeps the right source map. -/
theorem w1474NormalizedLiftObjDataKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input Y).rightSrc =
      input.normalizedLiftRightSrc Y :=
  rfl

/-- W1474's object-data family keeps the left factorization law. -/
theorem w1474NormalizedLiftObjDataKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input Y).left_fac =
      input.normalizedLiftLeftFac Y :=
  rfl

/-- W1474's object-data family keeps the right factorization law. -/
theorem w1474NormalizedLiftObjDataKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input Y).right_fac =
      input.normalizedLiftRightFac Y :=
  rfl

/-- W1474's raw lift blueprint keeps the constructed object-data family. -/
theorem w1474NormalizedLiftRawBlueprintKeepsConstructedObjData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).objData =
      normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input :=
  rfl

/-- W1474's raw lift blueprint keeps the map-data field. -/
theorem w1474NormalizedLiftRawBlueprintKeepsMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).mapData τ =
      input.normalizedLiftMapData τ :=
  rfl

/-- W1474's raw lift blueprint keeps the identity law. -/
theorem w1474NormalizedLiftRawBlueprintKeepsMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).map_id Y =
      input.normalizedLiftMapId Y :=
  rfl

/-- W1474's raw lift blueprint keeps the composition law. -/
theorem w1474NormalizedLiftRawBlueprintKeepsMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).map_comp τ σ =
      input.normalizedLiftMapComp τ σ :=
  rfl

/-- W1474's normalized lift blueprint keeps the constructed raw lift blueprint. -/
theorem w1474NormalizedLiftBlueprintKeepsConstructedRawBlueprint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).blueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input :=
  rfl

/-- W1474's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1474NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).obj_image X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1474's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1474NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).map_image τ =
      input.normalizedLiftMapImage τ :=
  rfl

/-- W1474's W1473 input keeps the first W718 component field. -/
theorem w1474W1473InputKeepsGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).globalClosedEmbeddingPi1 =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1474's W1473 input keeps the second W718 component field. -/
theorem w1474W1473InputKeepsGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).globalClosedEmbeddingPi2 =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1474's W1473 input keeps the third W718 component field. -/
theorem w1474W1473InputKeepsGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).globalClosedEmbeddingPi3 =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1474's W1473 input keeps W519 mapped-cokernel data. -/
theorem w1474W1473InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetLiftBlueprintFieldDataW1473
        (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input :=
  rfl

/-- W1474's W1473 input keeps the constructed object-data family. -/
theorem w1474W1473InputKeepsConstructedObjData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).normalizedLiftObjData =
      normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input :=
  rfl

/-- W1474's W1473 input keeps the map-data family. -/
theorem w1474W1473InputKeepsNormalizedLiftMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).normalizedLiftMapData τ =
      input.normalizedLiftMapData τ :=
  rfl

/-- W1474's W1473 input keeps the map identity law. -/
theorem w1474W1473InputKeepsNormalizedLiftMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).normalizedLiftMapId Y =
      input.normalizedLiftMapId Y :=
  rfl

/-- W1474's W1473 input keeps the map composition law. -/
theorem w1474W1473InputKeepsNormalizedLiftMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).normalizedLiftMapComp τ σ =
      input.normalizedLiftMapComp τ σ :=
  rfl

/-- W1474's W1473 input keeps the object-image normalization field. -/
theorem w1474W1473InputKeepsNormalizedLiftObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).normalizedLiftObjImage X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1474's W1473 input keeps the map-image normalization field. -/
theorem w1474W1473InputKeepsNormalizedLiftMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).normalizedLiftMapImage τ =
      input.normalizedLiftMapImage τ :=
  rfl

/-- W1474's W1473 input keeps target-difference surjectivity. -/
theorem w1474W1473InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1474's W1473 input keeps target-codomain compact no-univ membership. -/
theorem w1474W1473InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1474's W1473 input keeps the reconstructed localized right adjoint. -/
theorem w1474W1473InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    boundedHomotopyLocalizedRightAdjointOfW1473
        (w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1474 input :=
  rfl

/-- W1474's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1474LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1474 input :=
  rfl

/-- W1474's W986 construction keeps the constructed W973 closedness data. -/
theorem w1474TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input :=
  rfl

/-- W1474's constructed W987 provider projects to the constructed W730 data. -/
theorem w1474FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input :=
  rfl

/-- W1474's constructed W987 provider projects to the constructed W986 data. -/
theorem w1474FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        input :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputNamesW1474 :
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
    "normalized lift zero strict-preimage object source",
    "normalized lift one strict-preimage object source",
    "normalized lift zero comparison isomorphism",
    "normalized lift one comparison isomorphism",
    "normalized lift left source map",
    "normalized lift right source map",
    "normalized lift left factorization law",
    "normalized lift right factorization law",
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

theorem w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputNamesW1474_count :
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputNamesW1474.length =
      51 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionBundledObjectDataInputNamesW1474 :
    List String :=
  ["normalized lift object strict-preimage data family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionBundledObjectDataInputNamesW1474_count :
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionBundledObjectDataInputNamesW1474.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionObjectFieldInputNamesW1474 :
    List String :=
  ["normalized lift zero strict-preimage object source",
    "normalized lift one strict-preimage object source",
    "normalized lift zero comparison isomorphism",
    "normalized lift one comparison isomorphism",
    "normalized lift left source map",
    "normalized lift right source map",
    "normalized lift left factorization law",
    "normalized lift right factorization law"]

theorem w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionObjectFieldInputNamesW1474_count :
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionObjectFieldInputNamesW1474.length =
      8 :=
  rfl

/-- W1474 replaces one strict-preimage object-data family by its eight fields. -/
theorem w1474BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionSplitsObjectDataInput :
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionBundledObjectDataInputNamesW1474.length <
      w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionObjectFieldInputNamesW1474.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionBundledObjectDataInputNamesW1474_count,
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionObjectFieldInputNamesW1474_count]
  decide

/-- W1474 expands the W1473 input count after splitting the object-data family. -/
theorem w1474BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionExpandsW1473InputCount :
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputNamesW1473.length <
      w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputNamesW1474.length := by
  rw [
    w987BoundaryRelationTargetLiftBlueprintFieldDataConstructionInputNamesW1473_count,
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputNamesW1474_count]
  decide

/-- Current W1474 nonterminal strict-preimage object-field construction state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionStateW1474 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  objectDataInputNames : List String
  objectFieldInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1474 records the strict-preimage object-field construction path. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionStateW1474 :
    W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionStateW1474 where
  seed :=
    "w1474-w987-boundary-relation-target-strict-preimage-object-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474",
      "normalizedLiftObjDataOfFieldsW1474",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "boundedHomotopyLocalizedRightAdjointOfW1474",
      "w1473InputOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "fullDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474",
      "w1474GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1474GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1474GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1474ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1474ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1474MappedCokernelClosedEmbeddingProviderKeepsRawField",
      "w1474NormalizedLiftObjDataKeepsZeroSrc",
      "w1474NormalizedLiftObjDataKeepsOneSrc",
      "w1474NormalizedLiftObjDataKeepsZeroIso",
      "w1474NormalizedLiftObjDataKeepsOneIso",
      "w1474NormalizedLiftObjDataKeepsLeftSrc",
      "w1474NormalizedLiftObjDataKeepsRightSrc",
      "w1474NormalizedLiftObjDataKeepsLeftFac",
      "w1474NormalizedLiftObjDataKeepsRightFac",
      "w1474NormalizedLiftRawBlueprintKeepsConstructedObjData",
      "w1474NormalizedLiftRawBlueprintKeepsMapData",
      "w1474NormalizedLiftRawBlueprintKeepsMapId",
      "w1474NormalizedLiftRawBlueprintKeepsMapComp",
      "w1474NormalizedLiftBlueprintKeepsConstructedRawBlueprint",
      "w1474NormalizedLiftBlueprintKeepsObjImage",
      "w1474NormalizedLiftBlueprintKeepsMapImage",
      "w1474W1473InputKeepsGlobalClosedEmbeddingPi1",
      "w1474W1473InputKeepsGlobalClosedEmbeddingPi2",
      "w1474W1473InputKeepsGlobalClosedEmbeddingPi3",
      "w1474W1473InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1474W1473InputKeepsConstructedObjData",
      "w1474W1473InputKeepsNormalizedLiftMapData",
      "w1474W1473InputKeepsNormalizedLiftMapId",
      "w1474W1473InputKeepsNormalizedLiftMapComp",
      "w1474W1473InputKeepsNormalizedLiftObjImage",
      "w1474W1473InputKeepsNormalizedLiftMapImage",
      "w1474W1473InputKeepsTargetDifferenceSurjective",
      "w1474W1473InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1474W1473InputKeepsConstructedLocalizedRightAdjoint",
      "w1474LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1474TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1474FullDataKeepsConstructedBoundaryRelation",
      "w1474FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputNamesW1474_count",
      "w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionBundledObjectDataInputNamesW1474_count",
      "w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionObjectFieldInputNamesW1474_count",
      "w1474BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionSplitsObjectDataInput",
      "w1474BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionExpandsW1473InputCount"]
  constructionResult :=
    "proved: W1474 reconstructs the strict-preimage object-data family\
      from zero/one objects, comparison isomorphisms, source maps, and\
      factorization laws, then feeds that family into W1473"
  projectionResult :=
    "proved: the constructed object-data family projects back to the eight\
      strict-preimage object fields while W1473 preserves the raw lift\
      blueprint, localized-unit, boundary, and target/endpoint projections;\
      product success is still not claimed"
  objectDataInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionBundledObjectDataInputNamesW1474
  objectFieldInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionObjectFieldInputNamesW1474
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputNamesW1474
  productSuccessClaimed := false

theorem currentW1474W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionStateW1474.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
