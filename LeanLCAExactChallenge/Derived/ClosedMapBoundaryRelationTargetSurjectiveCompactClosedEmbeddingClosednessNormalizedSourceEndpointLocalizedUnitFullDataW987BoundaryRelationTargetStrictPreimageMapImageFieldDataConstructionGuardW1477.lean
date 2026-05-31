import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionGuardW1476

/-!
W1477 refines W1476 by constructing the normalized lift map-image
normalization law from componentwise zero/one map-image normalization laws,
then running the resulting data through the W1476 W987 construction.
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

/-- W1477 assembles one strict-preimage object datum from its constructor fields. -/
def normalizedLiftObjDataOfFieldsW1477
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

/-- W1477 assembles one strict-preimage map datum from its constructor fields. -/
def normalizedLiftMapDataOfFieldsW1477
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
    (zeroMap :
      ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (_τ : Y ⟶ Z),
        zeroSrc Y ⟶ zeroSrc Z)
    (oneMap :
      ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (_τ : Y ⟶ Z),
        oneSrc Y ⟶ oneSrc Z)
    (zeroMapFac :
      ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
        (Dbounded.localization MetrizableLCA.{0}).map (zeroMap τ) =
          (zeroIso Y).hom ≫
            τ.app WalkingParallelPair.zero ≫
              (zeroIso Z).inv)
    (oneMapFac :
      ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
        (Dbounded.localization MetrizableLCA.{0}).map (oneMap τ) =
          (oneIso Y).hom ≫
            τ.app WalkingParallelPair.one ≫
              (oneIso Z).inv)
    (leftNaturality :
      ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
        leftSrc Y ≫ oneMap τ =
          zeroMap τ ≫ leftSrc Z)
    (rightNaturality :
      ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
        rightSrc Y ≫ oneMap τ =
          zeroMap τ ≫ rightSrc Z)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
      (normalizedLiftObjDataOfFieldsW1477 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Y)
      (normalizedLiftObjDataOfFieldsW1477 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Z)
      τ where
  zeroMap := zeroMap τ
  oneMap := oneMap τ
  zero_fac := zeroMapFac τ
  one_fac := oneMapFac τ
  left_naturality := leftNaturality τ
  right_naturality := rightNaturality τ

/--
W1477 replaces W1476's bundled normalized lift map-image law by componentwise
zero/one map-image laws.
-/
structure W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477 :
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
  normalizedLiftZeroMap :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (_τ : Y ⟶ Z),
      normalizedLiftZeroSrc Y ⟶ normalizedLiftZeroSrc Z
  normalizedLiftOneMap :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (_τ : Y ⟶ Z),
      normalizedLiftOneSrc Y ⟶ normalizedLiftOneSrc Z
  normalizedLiftZeroMapFac :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      (Dbounded.localization MetrizableLCA.{0}).map
          (normalizedLiftZeroMap τ) =
        (normalizedLiftZeroIso Y).hom ≫
          τ.app WalkingParallelPair.zero ≫
            (normalizedLiftZeroIso Z).inv
  normalizedLiftOneMapFac :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      (Dbounded.localization MetrizableLCA.{0}).map
          (normalizedLiftOneMap τ) =
        (normalizedLiftOneIso Y).hom ≫
          τ.app WalkingParallelPair.one ≫
            (normalizedLiftOneIso Z).inv
  normalizedLiftLeftNaturality :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      normalizedLiftLeftSrc Y ≫ normalizedLiftOneMap τ =
        normalizedLiftZeroMap τ ≫ normalizedLiftLeftSrc Z
  normalizedLiftRightNaturality :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      normalizedLiftRightSrc Y ≫ normalizedLiftOneMap τ =
        normalizedLiftZeroMap τ ≫ normalizedLiftRightSrc Z
  normalizedLiftZeroMapId :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      normalizedLiftZeroMap (𝟙 Y) = 𝟙 (normalizedLiftZeroSrc Y)
  normalizedLiftOneMapId :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      normalizedLiftOneMap (𝟙 Y) = 𝟙 (normalizedLiftOneSrc Y)
  normalizedLiftZeroMapComp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      normalizedLiftZeroMap (τ ≫ σ) =
        normalizedLiftZeroMap τ ≫ normalizedLiftZeroMap σ
  normalizedLiftOneMapComp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      normalizedLiftOneMap (τ ≫ σ) =
        normalizedLiftOneMap τ ≫ normalizedLiftOneMap σ
  normalizedLiftObjImage :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (normalizedLiftObjDataOfFieldsW1477 normalizedLiftZeroSrc
        normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
        normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
        normalizedLiftRightFac
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  normalizedLiftZeroMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      ((normalizedLiftMapDataOfFieldsW1477 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImage Y)).app WalkingParallelPair.zero =
      (eqToHom (normalizedLiftObjImage X) ≫ τ).app WalkingParallelPair.zero
  normalizedLiftOneMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      ((normalizedLiftMapDataOfFieldsW1477 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImage Y)).app WalkingParallelPair.one =
      (eqToHom (normalizedLiftObjImage X) ≫ τ).app WalkingParallelPair.one
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

/-- W1477 keeps the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1477 builds the W519 provider from its raw closed-embedding field. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding := input.mappedExplicitCokernelClosedEmbedding

/-- W1477 builds the strict-preimage object-data family from its fields. -/
def normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y :=
  fun Y =>
    normalizedLiftObjDataOfFieldsW1477 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac Y

/-- W1477 builds the strict-preimage map-data family from its fields. -/
def normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input Y)
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input Z)
        τ :=
  fun {_Y _Z} τ =>
    normalizedLiftMapDataOfFieldsW1477 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroMap
      input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
      input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
      input.normalizedLiftRightNaturality τ

/-- W1477 derives the raw lift map identity law from zero/one component laws. -/
def normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input (𝟙 Y)).natTrans =
        𝟙 (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input Y).diagram :=
  fun Y => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477,
        normalizedLiftObjDataOfFieldsW1477,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477,
        normalizedLiftMapDataOfFieldsW1477,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapId Y
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477,
        normalizedLiftObjDataOfFieldsW1477,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477,
        normalizedLiftMapDataOfFieldsW1477,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapId Y

/-- W1477 derives the raw lift map composition law from zero/one component laws. -/
def normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input (τ ≫ σ)).natTrans =
        (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input τ).natTrans ≫
          (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
            input σ).natTrans :=
  fun {_Y _Z _T} τ σ => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477,
        normalizedLiftObjDataOfFieldsW1477,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477,
        normalizedLiftMapDataOfFieldsW1477,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapComp τ σ
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477,
        normalizedLiftObjDataOfFieldsW1477,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477,
        normalizedLiftMapDataOfFieldsW1477,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapComp τ σ

/-- W1477 derives the normalized lift map-image law from zero/one components. -/
def normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
      (τ : X ⟶ Y),
      (normalizedLiftMapDataOfFieldsW1477 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (input.normalizedLiftObjImage Y) =
      eqToHom (input.normalizedLiftObjImage X) ≫ τ :=
  fun {_X _Y} τ => by
    apply NatTrans.ext
    funext j
    cases j
    · exact input.normalizedLiftZeroMapImage τ
    · exact input.normalizedLiftOneMapImage τ

/-- W1477 builds the raw lift blueprint from its object and functorial fields. -/
def normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData :=
    normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input
  mapData :=
    normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input
  map_id :=
    normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input
  map_comp :=
    normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input

/-- W1477 builds the normalized lift blueprint from the raw lift fields. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input
  obj_image := input.normalizedLiftObjImage
  map_image :=
    normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input

/-- W1477 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input

/-- W1477 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1477 builds the W1476 input after reconstructing the map-data family. -/
def w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476 where
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
  normalizedLiftZeroSrc := input.normalizedLiftZeroSrc
  normalizedLiftOneSrc := input.normalizedLiftOneSrc
  normalizedLiftZeroIso := input.normalizedLiftZeroIso
  normalizedLiftOneIso := input.normalizedLiftOneIso
  normalizedLiftLeftSrc := input.normalizedLiftLeftSrc
  normalizedLiftRightSrc := input.normalizedLiftRightSrc
  normalizedLiftLeftFac := input.normalizedLiftLeftFac
  normalizedLiftRightFac := input.normalizedLiftRightFac
  normalizedLiftZeroMap := input.normalizedLiftZeroMap
  normalizedLiftOneMap := input.normalizedLiftOneMap
  normalizedLiftZeroMapFac := input.normalizedLiftZeroMapFac
  normalizedLiftOneMapFac := input.normalizedLiftOneMapFac
  normalizedLiftLeftNaturality := input.normalizedLiftLeftNaturality
  normalizedLiftRightNaturality := input.normalizedLiftRightNaturality
  normalizedLiftZeroMapId := input.normalizedLiftZeroMapId
  normalizedLiftOneMapId := input.normalizedLiftOneMapId
  normalizedLiftZeroMapComp := input.normalizedLiftZeroMapComp
  normalizedLiftOneMapComp := input.normalizedLiftOneMapComp
  normalizedLiftObjImage := input.normalizedLiftObjImage
  normalizedLiftMapImage :=
    normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
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

/-- W1477 builds W945 localized-unit data through W1476. -/
def localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input)

/-- W1477 builds W730 boundary/relation data through W1476. -/
def boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input)

/-- W1477 builds W986 target/endpoint data through W1476. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input)

/-- W1477 builds W987 full data through W1476. -/
noncomputable def fullDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
      input)

/-- W1477's constructed W718 provider keeps the first component field. -/
theorem w1477GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1477's constructed W718 provider keeps the second component field. -/
theorem w1477GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1477's constructed W718 provider keeps the third component field. -/
theorem w1477GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1477's constructed W973 data keeps the constructed W718 provider. -/
theorem w1477ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input :=
  rfl

/-- W1477's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1477ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input :=
  rfl

/-- W1477's constructed W519 provider keeps the raw closed-embedding field. -/
theorem w1477MappedCokernelClosedEmbeddingProviderKeepsRawField
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).isClosedEmbedding f =
      input.mappedExplicitCokernelClosedEmbedding f :=
  rfl

/-- W1477's object-data family keeps the zero object field. -/
theorem w1477NormalizedLiftObjDataKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input Y).zeroSrc =
      input.normalizedLiftZeroSrc Y :=
  rfl

/-- W1477's object-data family keeps the one object field. -/
theorem w1477NormalizedLiftObjDataKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input Y).oneSrc =
      input.normalizedLiftOneSrc Y :=
  rfl

/-- W1477's object-data family keeps the zero comparison isomorphism. -/
theorem w1477NormalizedLiftObjDataKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input Y).zeroIso =
      input.normalizedLiftZeroIso Y :=
  rfl

/-- W1477's object-data family keeps the one comparison isomorphism. -/
theorem w1477NormalizedLiftObjDataKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input Y).oneIso =
      input.normalizedLiftOneIso Y :=
  rfl

/-- W1477's object-data family keeps the left source map. -/
theorem w1477NormalizedLiftObjDataKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input Y).leftSrc =
      input.normalizedLiftLeftSrc Y :=
  rfl

/-- W1477's object-data family keeps the right source map. -/
theorem w1477NormalizedLiftObjDataKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input Y).rightSrc =
      input.normalizedLiftRightSrc Y :=
  rfl

/-- W1477's object-data family keeps the left factorization law. -/
theorem w1477NormalizedLiftObjDataKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input Y).left_fac =
      input.normalizedLiftLeftFac Y :=
  rfl

/-- W1477's object-data family keeps the right factorization law. -/
theorem w1477NormalizedLiftObjDataKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input Y).right_fac =
      input.normalizedLiftRightFac Y :=
  rfl

/-- W1477's map-data family keeps the zero map field. -/
theorem w1477NormalizedLiftMapDataKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ).zeroMap =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1477's map-data family keeps the one map field. -/
theorem w1477NormalizedLiftMapDataKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ).oneMap =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1477's map-data family keeps the zero-map factorization law. -/
theorem w1477NormalizedLiftMapDataKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ).zero_fac =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1477's map-data family keeps the one-map factorization law. -/
theorem w1477NormalizedLiftMapDataKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ).one_fac =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1477's map-data family keeps the left naturality law. -/
theorem w1477NormalizedLiftMapDataKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ).left_naturality =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1477's map-data family keeps the right naturality law. -/
theorem w1477NormalizedLiftMapDataKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ).right_naturality =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1477's raw lift blueprint keeps the constructed object-data family. -/
theorem w1477NormalizedLiftRawBlueprintKeepsConstructedObjData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).objData =
      normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input :=
  rfl

/-- W1477's raw lift blueprint keeps the constructed map-data family. -/
theorem w1477NormalizedLiftRawBlueprintKeepsConstructedMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).mapData τ =
      normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ :=
  rfl

/-- W1477's raw lift blueprint keeps the constructed identity law. -/
theorem w1477NormalizedLiftRawBlueprintKeepsMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).map_id Y =
      normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input Y :=
  rfl

/-- W1477's raw lift blueprint keeps the constructed composition law. -/
theorem w1477NormalizedLiftRawBlueprintKeepsMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).map_comp τ σ =
      normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ σ :=
  rfl

/-- W1477's normalized lift blueprint keeps the constructed raw lift blueprint. -/
theorem w1477NormalizedLiftBlueprintKeepsConstructedRawBlueprint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).blueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input :=
  rfl

/-- W1477's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1477NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).obj_image X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1477's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1477NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).map_image τ =
      normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ :=
  rfl

/-- W1477's input keeps the zero component map-image normalization law. -/
theorem w1477NormalizedLiftMapImageKeepsZeroComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1477 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (input.normalizedLiftObjImage Y)).app WalkingParallelPair.zero =
      (eqToHom (input.normalizedLiftObjImage X) ≫ τ).app WalkingParallelPair.zero :=
  input.normalizedLiftZeroMapImage τ

/-- W1477's input keeps the one component map-image normalization law. -/
theorem w1477NormalizedLiftMapImageKeepsOneComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1477 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (input.normalizedLiftObjImage Y)).app WalkingParallelPair.one =
      (eqToHom (input.normalizedLiftObjImage X) ≫ τ).app WalkingParallelPair.one :=
  input.normalizedLiftOneMapImage τ

/-- W1477's W1476 input keeps the first W718 component field. -/
theorem w1477W1476InputKeepsGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).globalClosedEmbeddingPi1 =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1477's W1476 input keeps the second W718 component field. -/
theorem w1477W1476InputKeepsGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).globalClosedEmbeddingPi2 =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1477's W1476 input keeps the third W718 component field. -/
theorem w1477W1476InputKeepsGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).globalClosedEmbeddingPi3 =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1477's W1476 input keeps W519 mapped-cokernel data. -/
theorem w1477W1476InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input :=
  rfl

/-- W1477's W1476 input keeps the zero source object field. -/
theorem w1477W1476InputKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftZeroSrc =
      input.normalizedLiftZeroSrc :=
  rfl

/-- W1477's W1476 input keeps the one source object field. -/
theorem w1477W1476InputKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftOneSrc =
      input.normalizedLiftOneSrc :=
  rfl

/-- W1477's W1476 input keeps the zero comparison isomorphism. -/
theorem w1477W1476InputKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftZeroIso =
      input.normalizedLiftZeroIso :=
  rfl

/-- W1477's W1476 input keeps the one comparison isomorphism. -/
theorem w1477W1476InputKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftOneIso =
      input.normalizedLiftOneIso :=
  rfl

/-- W1477's W1476 input keeps the left source map. -/
theorem w1477W1476InputKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftLeftSrc =
      input.normalizedLiftLeftSrc :=
  rfl

/-- W1477's W1476 input keeps the right source map. -/
theorem w1477W1476InputKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftRightSrc =
      input.normalizedLiftRightSrc :=
  rfl

/-- W1477's W1476 input keeps the left factorization law. -/
theorem w1477W1476InputKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftLeftFac =
      input.normalizedLiftLeftFac :=
  rfl

/-- W1477's W1476 input keeps the right factorization law. -/
theorem w1477W1476InputKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftRightFac =
      input.normalizedLiftRightFac :=
  rfl

/-- W1477's W1476 input keeps the zero map field. -/
theorem w1477W1476InputKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftZeroMap τ =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1477's W1476 input keeps the one map field. -/
theorem w1477W1476InputKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftOneMap τ =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1477's W1476 input keeps the zero-map factorization law. -/
theorem w1477W1476InputKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftZeroMapFac τ =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1477's W1476 input keeps the one-map factorization law. -/
theorem w1477W1476InputKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftOneMapFac τ =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1477's W1476 input keeps the left naturality law. -/
theorem w1477W1476InputKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftLeftNaturality τ =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1477's W1476 input keeps the right naturality law. -/
theorem w1477W1476InputKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftRightNaturality τ =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1477's W1476 input keeps the zero-map identity law. -/
theorem w1477W1476InputKeepsZeroMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftZeroMapId Y =
      input.normalizedLiftZeroMapId Y :=
  rfl

/-- W1477's W1476 input keeps the one-map identity law. -/
theorem w1477W1476InputKeepsOneMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftOneMapId Y =
      input.normalizedLiftOneMapId Y :=
  rfl

/-- W1477's W1476 input keeps the zero-map composition law. -/
theorem w1477W1476InputKeepsZeroMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftZeroMapComp τ σ =
      input.normalizedLiftZeroMapComp τ σ :=
  rfl

/-- W1477's W1476 input keeps the one-map composition law. -/
theorem w1477W1476InputKeepsOneMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftOneMapComp τ σ =
      input.normalizedLiftOneMapComp τ σ :=
  rfl

/-- W1477's W1476 input keeps the object-image normalization field. -/
theorem w1477W1476InputKeepsNormalizedLiftObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftObjImage X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1477's W1476 input keeps the map-image normalization field. -/
theorem w1477W1476InputKeepsNormalizedLiftMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).normalizedLiftMapImage τ =
      normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input τ :=
  rfl

/-- W1477's W1476 input keeps target-difference surjectivity. -/
theorem w1477W1476InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1477's W1476 input keeps target-codomain compact no-univ membership. -/
theorem w1477W1476InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1477's W1476 input keeps the reconstructed localized right adjoint. -/
theorem w1477W1476InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    boundedHomotopyLocalizedRightAdjointOfW1476
        (w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1477 input :=
  rfl

/-- W1477's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1477LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1477 input :=
  rfl

/-- W1477's W986 construction keeps the constructed W973 closedness data. -/
theorem w1477TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input :=
  rfl

/-- W1477's constructed W987 provider projects to the constructed W730 data. -/
theorem w1477FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input :=
  rfl

/-- W1477's constructed W987 provider projects to the constructed W986 data. -/
theorem w1477FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        input :=
  rfl

def w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477 :
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
    "normalized lift zero strict-preimage map family",
    "normalized lift one strict-preimage map family",
    "normalized lift zero-map factorization law",
    "normalized lift one-map factorization law",
    "normalized lift left naturality law",
    "normalized lift right naturality law",
    "normalized lift zero-map identity law",
    "normalized lift one-map identity law",
    "normalized lift zero-map composition law",
    "normalized lift one-map composition law",
    "normalized lift object-image normalization",
    "normalized lift zero-component map-image normalization",
    "normalized lift one-component map-image normalization",
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

theorem w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477_count :
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477.length =
      59 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionBundledMapImageInputNamesW1477 :
    List String :=
  ["normalized lift map-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionBundledMapImageInputNamesW1477_count :
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionBundledMapImageInputNamesW1477.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionComponentMapImageInputNamesW1477 :
    List String :=
  ["normalized lift zero-component map-image normalization",
    "normalized lift one-component map-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionComponentMapImageInputNamesW1477_count :
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionComponentMapImageInputNamesW1477.length =
      2 :=
  rfl

/-- W1477 replaces one map-image law by two component map-image laws. -/
theorem w1477BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionSplitsMapImageInput :
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionBundledMapImageInputNamesW1477.length <
      w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionComponentMapImageInputNamesW1477.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionBundledMapImageInputNamesW1477_count,
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionComponentMapImageInputNamesW1477_count]
  decide

/-- W1477 expands the W1476 input count after splitting the map-image law. -/
theorem w1477BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionExpandsW1476InputCount :
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputNamesW1476.length <
      w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputNamesW1476_count,
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477_count]
  decide

/-- Current W1477 nonterminal strict-preimage map-image construction state. -/
structure W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionStateW1477 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  mapImageInputNames : List String
  componentMapImageInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1477 records the strict-preimage map-image construction path. -/
def currentW987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionStateW1477 :
    W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionStateW1477 where
  seed :=
    "w1477-w987-boundary-relation-target-strict-preimage-map-image-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477",
      "normalizedLiftObjDataOfFieldsW1477",
      "normalizedLiftMapDataOfFieldsW1477",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "boundedHomotopyLocalizedRightAdjointOfW1477",
      "w1476InputOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "fullDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477",
      "w1477GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1477GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1477GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1477ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1477ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1477MappedCokernelClosedEmbeddingProviderKeepsRawField",
      "w1477NormalizedLiftObjDataKeepsZeroSrc",
      "w1477NormalizedLiftObjDataKeepsOneSrc",
      "w1477NormalizedLiftObjDataKeepsZeroIso",
      "w1477NormalizedLiftObjDataKeepsOneIso",
      "w1477NormalizedLiftObjDataKeepsLeftSrc",
      "w1477NormalizedLiftObjDataKeepsRightSrc",
      "w1477NormalizedLiftObjDataKeepsLeftFac",
      "w1477NormalizedLiftObjDataKeepsRightFac",
      "w1477NormalizedLiftMapDataKeepsZeroMap",
      "w1477NormalizedLiftMapDataKeepsOneMap",
      "w1477NormalizedLiftMapDataKeepsZeroMapFac",
      "w1477NormalizedLiftMapDataKeepsOneMapFac",
      "w1477NormalizedLiftMapDataKeepsLeftNaturality",
      "w1477NormalizedLiftMapDataKeepsRightNaturality",
      "w1477NormalizedLiftRawBlueprintKeepsConstructedObjData",
      "w1477NormalizedLiftRawBlueprintKeepsConstructedMapData",
      "w1477NormalizedLiftRawBlueprintKeepsMapId",
      "w1477NormalizedLiftRawBlueprintKeepsMapComp",
      "w1477NormalizedLiftBlueprintKeepsConstructedRawBlueprint",
      "w1477NormalizedLiftBlueprintKeepsObjImage",
      "w1477NormalizedLiftBlueprintKeepsMapImage",
      "w1477NormalizedLiftMapImageKeepsZeroComponent",
      "w1477NormalizedLiftMapImageKeepsOneComponent",
      "w1477W1476InputKeepsGlobalClosedEmbeddingPi1",
      "w1477W1476InputKeepsGlobalClosedEmbeddingPi2",
      "w1477W1476InputKeepsGlobalClosedEmbeddingPi3",
      "w1477W1476InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1477W1476InputKeepsZeroSrc",
      "w1477W1476InputKeepsOneSrc",
      "w1477W1476InputKeepsZeroIso",
      "w1477W1476InputKeepsOneIso",
      "w1477W1476InputKeepsLeftSrc",
      "w1477W1476InputKeepsRightSrc",
      "w1477W1476InputKeepsLeftFac",
      "w1477W1476InputKeepsRightFac",
      "w1477W1476InputKeepsZeroMap",
      "w1477W1476InputKeepsOneMap",
      "w1477W1476InputKeepsZeroMapFac",
      "w1477W1476InputKeepsOneMapFac",
      "w1477W1476InputKeepsLeftNaturality",
      "w1477W1476InputKeepsRightNaturality",
      "w1477W1476InputKeepsZeroMapId",
      "w1477W1476InputKeepsOneMapId",
      "w1477W1476InputKeepsZeroMapComp",
      "w1477W1476InputKeepsOneMapComp",
      "w1477W1476InputKeepsNormalizedLiftObjImage",
      "w1477W1476InputKeepsNormalizedLiftMapImage",
      "w1477W1476InputKeepsTargetDifferenceSurjective",
      "w1477W1476InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1477W1476InputKeepsConstructedLocalizedRightAdjoint",
      "w1477LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1477TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1477FullDataKeepsConstructedBoundaryRelation",
      "w1477FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477_count",
      "w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionBundledMapImageInputNamesW1477_count",
      "w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionComponentMapImageInputNamesW1477_count",
      "w1477BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionSplitsMapImageInput",
      "w1477BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionExpandsW1476InputCount"]
  constructionResult :=
    "proved: W1477 reconstructs the normalized lift map-image law from\
      zero/one component map-image laws, then feeds that law into W1476"
  projectionResult :=
    "proved: W1477's derived map-image law is used by the normalized lift\
      blueprint and by the W1476 input while W1476 preserves the raw lift\
      blueprint, localized-unit, boundary, and target/endpoint projections;\
      product success is still not claimed"
  mapImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionBundledMapImageInputNamesW1477
  componentMapImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionComponentMapImageInputNamesW1477
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477
  productSuccessClaimed := false

theorem currentW1477W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionStateW1477.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
