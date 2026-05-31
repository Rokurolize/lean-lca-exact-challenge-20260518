import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionGuardW1475

/-!
W1476 refines W1475 by constructing the raw lift map identity and composition
laws from componentwise zero/one map identity and composition laws, then
running the resulting data through the W1475 W987 construction.
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

/-- W1476 assembles one strict-preimage object datum from its constructor fields. -/
def normalizedLiftObjDataOfFieldsW1476
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

/-- W1476 assembles one strict-preimage map datum from its constructor fields. -/
def normalizedLiftMapDataOfFieldsW1476
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
      (normalizedLiftObjDataOfFieldsW1476 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Y)
      (normalizedLiftObjDataOfFieldsW1476 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Z)
      τ where
  zeroMap := zeroMap τ
  oneMap := oneMap τ
  zero_fac := zeroMapFac τ
  one_fac := oneMapFac τ
  left_naturality := leftNaturality τ
  right_naturality := rightNaturality τ

/--
W1476 replaces W1475's bundled raw lift map identity and composition laws by
componentwise zero/one map identity and composition laws.
-/
structure W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476 :
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
      (normalizedLiftObjDataOfFieldsW1476 normalizedLiftZeroSrc
        normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
        normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
        normalizedLiftRightFac
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  normalizedLiftMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (normalizedLiftMapDataOfFieldsW1476 normalizedLiftZeroSrc
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

/-- W1476 keeps the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1476 builds the W519 provider from its raw closed-embedding field. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding := input.mappedExplicitCokernelClosedEmbedding

/-- W1476 builds the strict-preimage object-data family from its fields. -/
def normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y :=
  fun Y =>
    normalizedLiftObjDataOfFieldsW1476 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac Y

/-- W1476 builds the strict-preimage map-data family from its fields. -/
def normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input Y)
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input Z)
        τ :=
  fun {_Y _Z} τ =>
    normalizedLiftMapDataOfFieldsW1476 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroMap
      input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
      input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
      input.normalizedLiftRightNaturality τ

/-- W1476 derives the raw lift map identity law from zero/one component laws. -/
def normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input (𝟙 Y)).natTrans =
        𝟙 (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input Y).diagram :=
  fun Y => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476,
        normalizedLiftObjDataOfFieldsW1476,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476,
        normalizedLiftMapDataOfFieldsW1476,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapId Y
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476,
        normalizedLiftObjDataOfFieldsW1476,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476,
        normalizedLiftMapDataOfFieldsW1476,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapId Y

/-- W1476 derives the raw lift map composition law from zero/one component laws. -/
def normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input (τ ≫ σ)).natTrans =
        (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input τ).natTrans ≫
          (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
            input σ).natTrans :=
  fun {_Y _Z _T} τ σ => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476,
        normalizedLiftObjDataOfFieldsW1476,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476,
        normalizedLiftMapDataOfFieldsW1476,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapComp τ σ
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476,
        normalizedLiftObjDataOfFieldsW1476,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476,
        normalizedLiftMapDataOfFieldsW1476,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapComp τ σ

/-- W1476 builds the raw lift blueprint from its object and functorial fields. -/
def normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData :=
    normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input
  mapData :=
    normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input
  map_id :=
    normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input
  map_comp :=
    normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input

/-- W1476 builds the normalized lift blueprint from the raw lift fields. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input
  obj_image := input.normalizedLiftObjImage
  map_image := input.normalizedLiftMapImage

/-- W1476 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input

/-- W1476 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1476 builds the W1475 input after reconstructing the map-data family. -/
def w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    W987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputW1475 where
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
  normalizedLiftMapId :=
    normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input
  normalizedLiftMapComp :=
    normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
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

/-- W1476 builds W945 localized-unit data through W1475. -/
def localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input)

/-- W1476 builds W730 boundary/relation data through W1475. -/
def boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input)

/-- W1476 builds W986 target/endpoint data through W1475. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input)

/-- W1476 builds W987 full data through W1475. -/
noncomputable def fullDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
      input)

/-- W1476's constructed W718 provider keeps the first component field. -/
theorem w1476GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1476's constructed W718 provider keeps the second component field. -/
theorem w1476GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1476's constructed W718 provider keeps the third component field. -/
theorem w1476GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1476's constructed W973 data keeps the constructed W718 provider. -/
theorem w1476ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input :=
  rfl

/-- W1476's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1476ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input :=
  rfl

/-- W1476's constructed W519 provider keeps the raw closed-embedding field. -/
theorem w1476MappedCokernelClosedEmbeddingProviderKeepsRawField
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).isClosedEmbedding f =
      input.mappedExplicitCokernelClosedEmbedding f :=
  rfl

/-- W1476's object-data family keeps the zero object field. -/
theorem w1476NormalizedLiftObjDataKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y).zeroSrc =
      input.normalizedLiftZeroSrc Y :=
  rfl

/-- W1476's object-data family keeps the one object field. -/
theorem w1476NormalizedLiftObjDataKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y).oneSrc =
      input.normalizedLiftOneSrc Y :=
  rfl

/-- W1476's object-data family keeps the zero comparison isomorphism. -/
theorem w1476NormalizedLiftObjDataKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y).zeroIso =
      input.normalizedLiftZeroIso Y :=
  rfl

/-- W1476's object-data family keeps the one comparison isomorphism. -/
theorem w1476NormalizedLiftObjDataKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y).oneIso =
      input.normalizedLiftOneIso Y :=
  rfl

/-- W1476's object-data family keeps the left source map. -/
theorem w1476NormalizedLiftObjDataKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y).leftSrc =
      input.normalizedLiftLeftSrc Y :=
  rfl

/-- W1476's object-data family keeps the right source map. -/
theorem w1476NormalizedLiftObjDataKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y).rightSrc =
      input.normalizedLiftRightSrc Y :=
  rfl

/-- W1476's object-data family keeps the left factorization law. -/
theorem w1476NormalizedLiftObjDataKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y).left_fac =
      input.normalizedLiftLeftFac Y :=
  rfl

/-- W1476's object-data family keeps the right factorization law. -/
theorem w1476NormalizedLiftObjDataKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y).right_fac =
      input.normalizedLiftRightFac Y :=
  rfl

/-- W1476's map-data family keeps the zero map field. -/
theorem w1476NormalizedLiftMapDataKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input τ).zeroMap =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1476's map-data family keeps the one map field. -/
theorem w1476NormalizedLiftMapDataKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input τ).oneMap =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1476's map-data family keeps the zero-map factorization law. -/
theorem w1476NormalizedLiftMapDataKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input τ).zero_fac =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1476's map-data family keeps the one-map factorization law. -/
theorem w1476NormalizedLiftMapDataKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input τ).one_fac =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1476's map-data family keeps the left naturality law. -/
theorem w1476NormalizedLiftMapDataKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input τ).left_naturality =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1476's map-data family keeps the right naturality law. -/
theorem w1476NormalizedLiftMapDataKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input τ).right_naturality =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1476's raw lift blueprint keeps the constructed object-data family. -/
theorem w1476NormalizedLiftRawBlueprintKeepsConstructedObjData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).objData =
      normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input :=
  rfl

/-- W1476's raw lift blueprint keeps the constructed map-data family. -/
theorem w1476NormalizedLiftRawBlueprintKeepsConstructedMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).mapData τ =
      normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input τ :=
  rfl

/-- W1476's raw lift blueprint keeps the constructed identity law. -/
theorem w1476NormalizedLiftRawBlueprintKeepsMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).map_id Y =
      normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y :=
  rfl

/-- W1476's raw lift blueprint keeps the constructed composition law. -/
theorem w1476NormalizedLiftRawBlueprintKeepsMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).map_comp τ σ =
      normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input τ σ :=
  rfl

/-- W1476's normalized lift blueprint keeps the constructed raw lift blueprint. -/
theorem w1476NormalizedLiftBlueprintKeepsConstructedRawBlueprint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).blueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input :=
  rfl

/-- W1476's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1476NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).obj_image X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1476's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1476NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).map_image τ =
      input.normalizedLiftMapImage τ :=
  rfl

/-- W1476's W1475 input keeps the first W718 component field. -/
theorem w1476W1475InputKeepsGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).globalClosedEmbeddingPi1 =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1476's W1475 input keeps the second W718 component field. -/
theorem w1476W1475InputKeepsGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).globalClosedEmbeddingPi2 =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1476's W1475 input keeps the third W718 component field. -/
theorem w1476W1475InputKeepsGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).globalClosedEmbeddingPi3 =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1476's W1475 input keeps W519 mapped-cokernel data. -/
theorem w1476W1475InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFieldDataW1475
        (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input :=
  rfl

/-- W1476's W1475 input keeps the zero source object field. -/
theorem w1476W1475InputKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftZeroSrc =
      input.normalizedLiftZeroSrc :=
  rfl

/-- W1476's W1475 input keeps the one source object field. -/
theorem w1476W1475InputKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftOneSrc =
      input.normalizedLiftOneSrc :=
  rfl

/-- W1476's W1475 input keeps the zero comparison isomorphism. -/
theorem w1476W1475InputKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftZeroIso =
      input.normalizedLiftZeroIso :=
  rfl

/-- W1476's W1475 input keeps the one comparison isomorphism. -/
theorem w1476W1475InputKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftOneIso =
      input.normalizedLiftOneIso :=
  rfl

/-- W1476's W1475 input keeps the left source map. -/
theorem w1476W1475InputKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftLeftSrc =
      input.normalizedLiftLeftSrc :=
  rfl

/-- W1476's W1475 input keeps the right source map. -/
theorem w1476W1475InputKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftRightSrc =
      input.normalizedLiftRightSrc :=
  rfl

/-- W1476's W1475 input keeps the left factorization law. -/
theorem w1476W1475InputKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftLeftFac =
      input.normalizedLiftLeftFac :=
  rfl

/-- W1476's W1475 input keeps the right factorization law. -/
theorem w1476W1475InputKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftRightFac =
      input.normalizedLiftRightFac :=
  rfl

/-- W1476's W1475 input keeps the zero map field. -/
theorem w1476W1475InputKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftZeroMap τ =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1476's W1475 input keeps the one map field. -/
theorem w1476W1475InputKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftOneMap τ =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1476's W1475 input keeps the zero-map factorization law. -/
theorem w1476W1475InputKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftZeroMapFac τ =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1476's W1475 input keeps the one-map factorization law. -/
theorem w1476W1475InputKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftOneMapFac τ =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1476's W1475 input keeps the left naturality law. -/
theorem w1476W1475InputKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftLeftNaturality τ =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1476's W1475 input keeps the right naturality law. -/
theorem w1476W1475InputKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftRightNaturality τ =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1476's W1475 input keeps the constructed map identity law. -/
theorem w1476W1475InputKeepsNormalizedLiftMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftMapId Y =
      normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input Y :=
  rfl

/-- W1476's W1475 input keeps the constructed map composition law. -/
theorem w1476W1475InputKeepsNormalizedLiftMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftMapComp τ σ =
      normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input τ σ :=
  rfl

/-- W1476's W1475 input keeps the object-image normalization field. -/
theorem w1476W1475InputKeepsNormalizedLiftObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftObjImage X =
      input.normalizedLiftObjImage X :=
  rfl

/-- W1476's W1475 input keeps the map-image normalization field. -/
theorem w1476W1475InputKeepsNormalizedLiftMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).normalizedLiftMapImage τ =
      input.normalizedLiftMapImage τ :=
  rfl

/-- W1476's W1475 input keeps target-difference surjectivity. -/
theorem w1476W1475InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1476's W1475 input keeps target-codomain compact no-univ membership. -/
theorem w1476W1475InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1476's W1475 input keeps the reconstructed localized right adjoint. -/
theorem w1476W1475InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    boundedHomotopyLocalizedRightAdjointOfW1475
        (w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1476 input :=
  rfl

/-- W1476's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1476LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1476 input :=
  rfl

/-- W1476's W986 construction keeps the constructed W973 closedness data. -/
theorem w1476TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input :=
  rfl

/-- W1476's constructed W987 provider projects to the constructed W730 data. -/
theorem w1476FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input :=
  rfl

/-- W1476's constructed W987 provider projects to the constructed W986 data. -/
theorem w1476FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476
        input :=
  rfl

def w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputNamesW1476 :
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

theorem w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputNamesW1476_count :
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputNamesW1476.length =
      58 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionBundledFunctorialityInputNamesW1476 :
    List String :=
  ["normalized lift map identity law",
    "normalized lift map composition law"]

theorem w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionBundledFunctorialityInputNamesW1476_count :
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionBundledFunctorialityInputNamesW1476.length =
      2 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionComponentFunctorialityInputNamesW1476 :
    List String :=
  ["normalized lift zero-map identity law",
    "normalized lift one-map identity law",
    "normalized lift zero-map composition law",
    "normalized lift one-map composition law"]

theorem w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionComponentFunctorialityInputNamesW1476_count :
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionComponentFunctorialityInputNamesW1476.length =
      4 :=
  rfl

/-- W1476 replaces two raw lift functoriality laws by four component laws. -/
theorem w1476BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionSplitsFunctorialityInput :
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionBundledFunctorialityInputNamesW1476.length <
      w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionComponentFunctorialityInputNamesW1476.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionBundledFunctorialityInputNamesW1476_count,
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionComponentFunctorialityInputNamesW1476_count]
  decide

/-- W1476 expands the W1475 input count after splitting functoriality laws. -/
theorem w1476BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionExpandsW1475InputCount :
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputNamesW1475.length <
      w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputNamesW1476.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageMapFieldDataConstructionInputNamesW1475_count,
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputNamesW1476_count]
  decide

/-- Current W1476 nonterminal strict-preimage map-functoriality construction state. -/
structure W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionStateW1476 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  functorialityInputNames : List String
  componentFunctorialityInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1476 records the strict-preimage map-functoriality construction path. -/
def currentW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionStateW1476 :
    W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionStateW1476 where
  seed :=
    "w1476-w987-boundary-relation-target-strict-preimage-map-functoriality-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputW1476",
      "normalizedLiftObjDataOfFieldsW1476",
      "normalizedLiftMapDataOfFieldsW1476",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "boundedHomotopyLocalizedRightAdjointOfW1476",
      "w1475InputOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "fullDataOfW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataW1476",
      "w1476GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1476GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1476GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1476ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1476ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1476MappedCokernelClosedEmbeddingProviderKeepsRawField",
      "w1476NormalizedLiftObjDataKeepsZeroSrc",
      "w1476NormalizedLiftObjDataKeepsOneSrc",
      "w1476NormalizedLiftObjDataKeepsZeroIso",
      "w1476NormalizedLiftObjDataKeepsOneIso",
      "w1476NormalizedLiftObjDataKeepsLeftSrc",
      "w1476NormalizedLiftObjDataKeepsRightSrc",
      "w1476NormalizedLiftObjDataKeepsLeftFac",
      "w1476NormalizedLiftObjDataKeepsRightFac",
      "w1476NormalizedLiftMapDataKeepsZeroMap",
      "w1476NormalizedLiftMapDataKeepsOneMap",
      "w1476NormalizedLiftMapDataKeepsZeroMapFac",
      "w1476NormalizedLiftMapDataKeepsOneMapFac",
      "w1476NormalizedLiftMapDataKeepsLeftNaturality",
      "w1476NormalizedLiftMapDataKeepsRightNaturality",
      "w1476NormalizedLiftRawBlueprintKeepsConstructedObjData",
      "w1476NormalizedLiftRawBlueprintKeepsConstructedMapData",
      "w1476NormalizedLiftRawBlueprintKeepsMapId",
      "w1476NormalizedLiftRawBlueprintKeepsMapComp",
      "w1476NormalizedLiftBlueprintKeepsConstructedRawBlueprint",
      "w1476NormalizedLiftBlueprintKeepsObjImage",
      "w1476NormalizedLiftBlueprintKeepsMapImage",
      "w1476W1475InputKeepsGlobalClosedEmbeddingPi1",
      "w1476W1475InputKeepsGlobalClosedEmbeddingPi2",
      "w1476W1475InputKeepsGlobalClosedEmbeddingPi3",
      "w1476W1475InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1476W1475InputKeepsZeroSrc",
      "w1476W1475InputKeepsOneSrc",
      "w1476W1475InputKeepsZeroIso",
      "w1476W1475InputKeepsOneIso",
      "w1476W1475InputKeepsLeftSrc",
      "w1476W1475InputKeepsRightSrc",
      "w1476W1475InputKeepsLeftFac",
      "w1476W1475InputKeepsRightFac",
      "w1476W1475InputKeepsZeroMap",
      "w1476W1475InputKeepsOneMap",
      "w1476W1475InputKeepsZeroMapFac",
      "w1476W1475InputKeepsOneMapFac",
      "w1476W1475InputKeepsLeftNaturality",
      "w1476W1475InputKeepsRightNaturality",
      "w1476W1475InputKeepsNormalizedLiftMapId",
      "w1476W1475InputKeepsNormalizedLiftMapComp",
      "w1476W1475InputKeepsNormalizedLiftObjImage",
      "w1476W1475InputKeepsNormalizedLiftMapImage",
      "w1476W1475InputKeepsTargetDifferenceSurjective",
      "w1476W1475InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1476W1475InputKeepsConstructedLocalizedRightAdjoint",
      "w1476LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1476TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1476FullDataKeepsConstructedBoundaryRelation",
      "w1476FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputNamesW1476_count",
      "w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionBundledFunctorialityInputNamesW1476_count",
      "w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionComponentFunctorialityInputNamesW1476_count",
      "w1476BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionSplitsFunctorialityInput",
      "w1476BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionExpandsW1475InputCount"]
  constructionResult :=
    "proved: W1476 reconstructs raw lift map identity and composition\
      laws from zero/one component identity and composition laws, then\
      feeds those laws into W1475"
  projectionResult :=
    "proved: W1476's derived functoriality laws are used by the raw lift\
      blueprint and by the W1475 input while W1475 preserves the raw lift\
      blueprint, localized-unit, boundary, and target/endpoint projections;\
      product success is still not claimed"
  functorialityInputNames :=
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionBundledFunctorialityInputNamesW1476
  componentFunctorialityInputNames :=
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionComponentFunctorialityInputNamesW1476
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionInputNamesW1476
  productSuccessClaimed := false

theorem currentW1476W987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageMapFunctorialityFieldDataConstructionStateW1476.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
