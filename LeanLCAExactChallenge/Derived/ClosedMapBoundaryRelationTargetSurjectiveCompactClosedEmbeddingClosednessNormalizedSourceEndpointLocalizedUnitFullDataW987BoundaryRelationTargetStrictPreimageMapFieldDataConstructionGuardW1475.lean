import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionGuardW1474

/-!
W1475 refines W1474 by constructing the strict-preimage map-data family from
its zero/one maps, localization factorization laws, and naturality laws, then
running the resulting data through the W1474 W987 construction.
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

/-- W1475 assembles one strict-preimage object datum from its constructor fields. -/
def normalizedLiftObjDataOfFieldsW1475
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

/-- W1475 assembles one strict-preimage map datum from its constructor fields. -/
def normalizedLiftMapDataOfFieldsW1475
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
      (normalizedLiftObjDataOfFieldsW1475 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Y)
      (normalizedLiftObjDataOfFieldsW1475 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Z)
      τ where
  zeroMap := zeroMap τ
  oneMap := oneMap τ
  zero_fac := zeroMapFac τ
  one_fac := oneMapFac τ
  left_naturality := leftNaturality τ
  right_naturality := rightNaturality τ

/--
W1475 replaces W1474's bundled strict-preimage map-data family by the six
fields used to construct that family.
-/
structure W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475 :
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
  normalizedLiftMapId :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (normalizedLiftMapDataOfFieldsW1475 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (𝟙 Y)).natTrans =
        𝟙 (normalizedLiftObjDataOfFieldsW1475 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac Y).diagram
  normalizedLiftMapComp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (normalizedLiftMapDataOfFieldsW1475 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (τ ≫ σ)).natTrans =
        (normalizedLiftMapDataOfFieldsW1475 normalizedLiftZeroSrc
            normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
            normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
            normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
            normalizedLiftZeroMapFac normalizedLiftOneMapFac
            normalizedLiftLeftNaturality normalizedLiftRightNaturality
            τ).natTrans ≫
          (normalizedLiftMapDataOfFieldsW1475 normalizedLiftZeroSrc
            normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
            normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
            normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
            normalizedLiftZeroMapFac normalizedLiftOneMapFac
            normalizedLiftLeftNaturality normalizedLiftRightNaturality
            σ).natTrans
  normalizedLiftObjImage :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (normalizedLiftObjDataOfFieldsW1475 normalizedLiftZeroSrc
        normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
        normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
        normalizedLiftRightFac
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  normalizedLiftMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (normalizedLiftMapDataOfFieldsW1475 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
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

/-- W1475 keeps the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1475 builds the W519 provider from its raw closed-embedding field. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding := input.mappedExplicitCokernelClosedEmbedding

/-- W1475 builds the strict-preimage object-data family from its fields. -/
def normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y :=
  fun Y =>
    normalizedLiftObjDataOfFieldsW1475 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac Y

/-- W1475 builds the strict-preimage map-data family from its fields. -/
def normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input Y)
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input Z)
        τ :=
  fun {_Y _Z} τ =>
    normalizedLiftMapDataOfFieldsW1475 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroMap
      input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
      input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
      input.normalizedLiftRightNaturality τ

/-- W1475 builds the raw lift blueprint from its object and functorial fields. -/
def normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData :=
    normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input
  mapData :=
    normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input
  map_id := input.normalizedLiftMapId
  map_comp := input.normalizedLiftMapComp

/-- W1475 builds the normalized lift blueprint from the raw lift fields. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input
  obj_image := input.normalizedLiftObjImage
  map_image := input.normalizedLiftMapImage

/-- W1475 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input

/-- W1475 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1475 builds the W1474 input after reconstructing the map-data family. -/
def w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    W987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputW1474 where
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
  normalizedLiftMapData :=
    normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input
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

/-- W1475 builds W945 localized-unit data through W1474. -/
def localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input)

/-- W1475 builds W730 boundary/relation data through W1474. -/
def boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input)

/-- W1475 builds W986 target/endpoint data through W1474. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input)

/-- W1475 builds W987 full data through W1474. -/
noncomputable def fullDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
      input)

/-- W1475's constructed W718 provider keeps the first component field. -/
theorem w1475GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1475's constructed W718 provider keeps the second component field. -/
theorem w1475GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1475's constructed W718 provider keeps the third component field. -/
theorem w1475GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1475's constructed W973 data keeps the constructed W718 provider. -/
theorem w1475ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input :=
  rfl

/-- W1475's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1475ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input :=
  rfl

/-- W1475's constructed W519 provider keeps the raw closed-embedding field. -/
theorem w1475MappedCokernelClosedEmbeddingProviderKeepsRawField
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).isClosedEmbedding f =
      input.mappedExplicitCokernelClosedEmbedding f :=
  rfl

/-- W1475's object-data family keeps the zero object field. -/
theorem w1475NormalizedLiftObjDataKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input Y).zeroSrc =
      input.normalizedLiftZeroSrc Y :=
  rfl

/-- W1475's object-data family keeps the one object field. -/
theorem w1475NormalizedLiftObjDataKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input Y).oneSrc =
      input.normalizedLiftOneSrc Y :=
  rfl

/-- W1475's object-data family keeps the zero comparison isomorphism. -/
theorem w1475NormalizedLiftObjDataKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input Y).zeroIso =
      input.normalizedLiftZeroIso Y :=
  rfl

/-- W1475's object-data family keeps the one comparison isomorphism. -/
theorem w1475NormalizedLiftObjDataKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input Y).oneIso =
      input.normalizedLiftOneIso Y :=
  rfl

/-- W1475's object-data family keeps the left source map. -/
theorem w1475NormalizedLiftObjDataKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input Y).leftSrc =
      input.normalizedLiftLeftSrc Y :=
  rfl

/-- W1475's object-data family keeps the right source map. -/
theorem w1475NormalizedLiftObjDataKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input Y).rightSrc =
      input.normalizedLiftRightSrc Y :=
  rfl

/-- W1475's object-data family keeps the left factorization law. -/
theorem w1475NormalizedLiftObjDataKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input Y).left_fac =
      input.normalizedLiftLeftFac Y :=
  rfl

/-- W1475's object-data family keeps the right factorization law. -/
theorem w1475NormalizedLiftObjDataKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input Y).right_fac =
      input.normalizedLiftRightFac Y :=
  rfl

/-- W1475's map-data family keeps the zero map field. -/
theorem w1475NormalizedLiftMapDataKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input τ).zeroMap =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1475's map-data family keeps the one map field. -/
theorem w1475NormalizedLiftMapDataKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input τ).oneMap =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1475's map-data family keeps the zero-map factorization law. -/
theorem w1475NormalizedLiftMapDataKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input τ).zero_fac =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1475's map-data family keeps the one-map factorization law. -/
theorem w1475NormalizedLiftMapDataKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input τ).one_fac =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1475's map-data family keeps the left naturality law. -/
theorem w1475NormalizedLiftMapDataKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input τ).left_naturality =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1475's map-data family keeps the right naturality law. -/
theorem w1475NormalizedLiftMapDataKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input τ).right_naturality =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1475's raw lift blueprint keeps the constructed object-data family. -/
theorem w1475NormalizedLiftRawBlueprintKeepsConstructedObjData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).objData =
      normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input :=
  rfl

/-- W1475's raw lift blueprint keeps the constructed map-data family. -/
theorem w1475NormalizedLiftRawBlueprintKeepsConstructedMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).mapData τ =
      normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input τ :=
  rfl

/-- W1475's raw lift blueprint keeps the identity law. -/
theorem w1475NormalizedLiftRawBlueprintKeepsMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).map_id Y =
      input.normalizedLiftMapId Y :=
  rfl

/-- W1475's raw lift blueprint keeps the composition law. -/
theorem w1475NormalizedLiftRawBlueprintKeepsMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).map_comp τ σ =
      input.normalizedLiftMapComp τ σ :=
  rfl

/-- W1475's normalized lift blueprint keeps the constructed raw lift blueprint. -/
theorem w1475NormalizedLiftBlueprintKeepsConstructedRawBlueprint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).blueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input :=
  rfl

/-- W1475's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1475NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).obj_image X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1475's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1475NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).map_image τ =
      input.normalizedLiftMapImage τ :=
  rfl

/-- W1475's W1474 input keeps the first W718 component field. -/
theorem w1475W1474InputKeepsGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).globalClosedEmbeddingPi1 =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1475's W1474 input keeps the second W718 component field. -/
theorem w1475W1474InputKeepsGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).globalClosedEmbeddingPi2 =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1475's W1474 input keeps the third W718 component field. -/
theorem w1475W1474InputKeepsGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).globalClosedEmbeddingPi3 =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1475's W1474 input keeps W519 mapped-cokernel data. -/
theorem w1475W1474InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectFieldDataW1474
        (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input :=
  rfl

/-- W1475's W1474 input keeps the zero source object field. -/
theorem w1475W1474InputKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftZeroSrc =
      input.normalizedLiftZeroSrc :=
  rfl

/-- W1475's W1474 input keeps the one source object field. -/
theorem w1475W1474InputKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftOneSrc =
      input.normalizedLiftOneSrc :=
  rfl

/-- W1475's W1474 input keeps the zero comparison isomorphism. -/
theorem w1475W1474InputKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftZeroIso =
      input.normalizedLiftZeroIso :=
  rfl

/-- W1475's W1474 input keeps the one comparison isomorphism. -/
theorem w1475W1474InputKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftOneIso =
      input.normalizedLiftOneIso :=
  rfl

/-- W1475's W1474 input keeps the left source map. -/
theorem w1475W1474InputKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftLeftSrc =
      input.normalizedLiftLeftSrc :=
  rfl

/-- W1475's W1474 input keeps the right source map. -/
theorem w1475W1474InputKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftRightSrc =
      input.normalizedLiftRightSrc :=
  rfl

/-- W1475's W1474 input keeps the left factorization law. -/
theorem w1475W1474InputKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftLeftFac =
      input.normalizedLiftLeftFac :=
  rfl

/-- W1475's W1474 input keeps the right factorization law. -/
theorem w1475W1474InputKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftRightFac =
      input.normalizedLiftRightFac :=
  rfl

/-- W1475's W1474 input keeps the constructed map-data family. -/
theorem w1475W1474InputKeepsConstructedMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftMapData τ =
      normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input τ :=
  rfl

/-- W1475's W1474 input keeps the map identity law. -/
theorem w1475W1474InputKeepsNormalizedLiftMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftMapId Y =
      input.normalizedLiftMapId Y :=
  rfl

/-- W1475's W1474 input keeps the map composition law. -/
theorem w1475W1474InputKeepsNormalizedLiftMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftMapComp τ σ =
      input.normalizedLiftMapComp τ σ :=
  rfl

/-- W1475's W1474 input keeps the object-image normalization field. -/
theorem w1475W1474InputKeepsNormalizedLiftObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftObjImage X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1475's W1474 input keeps the map-image normalization field. -/
theorem w1475W1474InputKeepsNormalizedLiftMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).normalizedLiftMapImage τ =
      input.normalizedLiftMapImage τ :=
  rfl

/-- W1475's W1474 input keeps target-difference surjectivity. -/
theorem w1475W1474InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1475's W1474 input keeps target-codomain compact no-univ membership. -/
theorem w1475W1474InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1475's W1474 input keeps the reconstructed localized right adjoint. -/
theorem w1475W1474InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    boundedHomotopyLocalizedRightAdjointOfW1474
        (w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1475 input :=
  rfl

/-- W1475's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1475LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1475 input :=
  rfl

/-- W1475's W986 construction keeps the constructed W973 closedness data. -/
theorem w1475TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input :=
  rfl

/-- W1475's constructed W987 provider projects to the constructed W730 data. -/
theorem w1475FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input :=
  rfl

/-- W1475's constructed W987 provider projects to the constructed W986 data. -/
theorem w1475FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        input :=
  rfl

def w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputNamesW1475 :
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

theorem w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputNamesW1475_count :
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputNamesW1475.length =
      56 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionBundledMapDataInputNamesW1475 :
    List String :=
  ["normalized lift map strict-preimage data family"]

theorem w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionBundledMapDataInputNamesW1475_count :
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionBundledMapDataInputNamesW1475.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionMapFieldInputNamesW1475 :
    List String :=
  ["normalized lift zero strict-preimage map family",
    "normalized lift one strict-preimage map family",
    "normalized lift zero-map factorization law",
    "normalized lift one-map factorization law",
    "normalized lift left naturality law",
    "normalized lift right naturality law"]

theorem w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionMapFieldInputNamesW1475_count :
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionMapFieldInputNamesW1475.length =
      6 :=
  rfl

/-- W1475 replaces one strict-preimage map-data family by its six fields. -/
theorem w1475BoundaryRelationTargetStrictPreimageMapFieldDataConstructionSplitsMapDataInput :
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionBundledMapDataInputNamesW1475.length <
      w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionMapFieldInputNamesW1475.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionBundledMapDataInputNamesW1475_count,
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionMapFieldInputNamesW1475_count]
  decide

/-- W1475 expands the W1474 input count after splitting the map-data family. -/
theorem w1475BoundaryRelationTargetStrictPreimageMapFieldDataConstructionExpandsW1474InputCount :
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputNamesW1474.length <
      w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputNamesW1475.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectFieldDataConstructionInputNamesW1474_count,
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputNamesW1475_count]
  decide

/-- Current W1475 nonterminal strict-preimage map-field construction state. -/
structure W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionStateW1475 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  mapDataInputNames : List String
  mapFieldInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1475 records the strict-preimage map-field construction path. -/
def currentW987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionStateW1475 :
    W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionStateW1475 where
  seed :=
    "w1475-w987-boundary-relation-target-strict-preimage-map-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475",
      "normalizedLiftObjDataOfFieldsW1475",
      "normalizedLiftMapDataOfFieldsW1475",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "boundedHomotopyLocalizedRightAdjointOfW1475",
      "w1474InputOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "fullDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475",
      "w1475GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1475GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1475GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1475ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1475ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1475MappedCokernelClosedEmbeddingProviderKeepsRawField",
      "w1475NormalizedLiftObjDataKeepsZeroSrc",
      "w1475NormalizedLiftObjDataKeepsOneSrc",
      "w1475NormalizedLiftObjDataKeepsZeroIso",
      "w1475NormalizedLiftObjDataKeepsOneIso",
      "w1475NormalizedLiftObjDataKeepsLeftSrc",
      "w1475NormalizedLiftObjDataKeepsRightSrc",
      "w1475NormalizedLiftObjDataKeepsLeftFac",
      "w1475NormalizedLiftObjDataKeepsRightFac",
      "w1475NormalizedLiftMapDataKeepsZeroMap",
      "w1475NormalizedLiftMapDataKeepsOneMap",
      "w1475NormalizedLiftMapDataKeepsZeroMapFac",
      "w1475NormalizedLiftMapDataKeepsOneMapFac",
      "w1475NormalizedLiftMapDataKeepsLeftNaturality",
      "w1475NormalizedLiftMapDataKeepsRightNaturality",
      "w1475NormalizedLiftRawBlueprintKeepsConstructedObjData",
      "w1475NormalizedLiftRawBlueprintKeepsConstructedMapData",
      "w1475NormalizedLiftRawBlueprintKeepsMapId",
      "w1475NormalizedLiftRawBlueprintKeepsMapComp",
      "w1475NormalizedLiftBlueprintKeepsConstructedRawBlueprint",
      "w1475NormalizedLiftBlueprintKeepsObjImage",
      "w1475NormalizedLiftBlueprintKeepsMapImage",
      "w1475W1474InputKeepsGlobalClosedEmbeddingPi1",
      "w1475W1474InputKeepsGlobalClosedEmbeddingPi2",
      "w1475W1474InputKeepsGlobalClosedEmbeddingPi3",
      "w1475W1474InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1475W1474InputKeepsZeroSrc",
      "w1475W1474InputKeepsOneSrc",
      "w1475W1474InputKeepsZeroIso",
      "w1475W1474InputKeepsOneIso",
      "w1475W1474InputKeepsLeftSrc",
      "w1475W1474InputKeepsRightSrc",
      "w1475W1474InputKeepsLeftFac",
      "w1475W1474InputKeepsRightFac",
      "w1475W1474InputKeepsConstructedMapData",
      "w1475W1474InputKeepsNormalizedLiftMapId",
      "w1475W1474InputKeepsNormalizedLiftMapComp",
      "w1475W1474InputKeepsNormalizedLiftObjImage",
      "w1475W1474InputKeepsNormalizedLiftMapImage",
      "w1475W1474InputKeepsTargetDifferenceSurjective",
      "w1475W1474InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1475W1474InputKeepsConstructedLocalizedRightAdjoint",
      "w1475LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1475TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1475FullDataKeepsConstructedBoundaryRelation",
      "w1475FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputNamesW1475_count",
      "w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionBundledMapDataInputNamesW1475_count",
      "w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionMapFieldInputNamesW1475_count",
      "w1475BoundaryRelationTargetStrictPreimageMapFieldDataConstructionSplitsMapDataInput",
      "w1475BoundaryRelationTargetStrictPreimageMapFieldDataConstructionExpandsW1474InputCount"]
  constructionResult :=
    "proved: W1475 reconstructs the strict-preimage map-data family\
      from zero/one maps, localization factorization laws, and naturality\
      laws, then feeds that family into W1474"
  projectionResult :=
    "proved: the constructed map-data family projects back to the six\
      strict-preimage map fields while W1474 preserves the raw lift\
      blueprint, localized-unit, boundary, and target/endpoint projections;\
      product success is still not claimed"
  mapDataInputNames :=
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionBundledMapDataInputNamesW1475
  mapFieldInputNames :=
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionMapFieldInputNamesW1475
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputNamesW1475
  productSuccessClaimed := false

theorem currentW1475W987BoundaryRelationTargetStrictPreimageMapFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionStateW1475.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
