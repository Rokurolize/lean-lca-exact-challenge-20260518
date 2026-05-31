import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionGuardW1477

/-!
W1478 refines W1477 by constructing the normalized lift object-image
normalization law from componentwise object and arrow image laws, then
running the resulting data through the W1477 W987 construction.
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

/-- W1478 assembles one strict-preimage object datum from its constructor fields. -/
def normalizedLiftObjDataOfFieldsW1478
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

/-- W1478 assembles one strict-preimage map datum from its constructor fields. -/
def normalizedLiftMapDataOfFieldsW1478
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
      (normalizedLiftObjDataOfFieldsW1478 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Y)
      (normalizedLiftObjDataOfFieldsW1478 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Z)
      τ where
  zeroMap := zeroMap τ
  oneMap := oneMap τ
  zero_fac := zeroMapFac τ
  one_fac := oneMapFac τ
  left_naturality := leftNaturality τ
  right_naturality := rightNaturality τ

/-- W1478 derives object-image normalization from object and arrow components. -/
def normalizedLiftObjImageOfFieldsW1478
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
    (zeroObjImage :
      ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
        zeroSrc
            (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X) =
          X.obj WalkingParallelPair.zero)
    (oneObjImage :
      ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
        oneSrc
            (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X) =
          X.obj WalkingParallelPair.one)
    (leftObjImage :
      ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
        leftSrc
            (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X) =
          eqToHom (zeroObjImage X) ≫ X.map WalkingParallelPairHom.left ≫
            eqToHom (oneObjImage X).symm)
    (rightObjImage :
      ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
        rightSrc
            (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X) =
          eqToHom (zeroObjImage X) ≫ X.map WalkingParallelPairHom.right ≫
            eqToHom (oneObjImage X).symm)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfFieldsW1478 zeroSrc oneSrc zeroIso oneIso
      leftSrc rightSrc leftFac rightFac
      (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X := by
  refine CategoryTheory.Functor.ext (fun j => ?_) (fun _ _ f => ?_)
  · cases j
    · exact zeroObjImage X
    · exact oneObjImage X
  · cases f
    · simpa [normalizedLiftObjDataOfFieldsW1478,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        leftObjImage X
    · simpa [normalizedLiftObjDataOfFieldsW1478,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        rightObjImage X
    · simp

/--
W1478 replaces W1477's bundled normalized lift object-image law by componentwise
zero/one object and left/right arrow image laws.
-/
structure W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478 :
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
  normalizedLiftZeroObjImage :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      normalizedLiftZeroSrc
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X) =
        X.obj WalkingParallelPair.zero
  normalizedLiftOneObjImage :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      normalizedLiftOneSrc
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X) =
        X.obj WalkingParallelPair.one
  normalizedLiftLeftObjImage :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      normalizedLiftLeftSrc
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X) =
        eqToHom (normalizedLiftZeroObjImage X) ≫
          X.map WalkingParallelPairHom.left ≫
            eqToHom (normalizedLiftOneObjImage X).symm
  normalizedLiftRightObjImage :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      normalizedLiftRightSrc
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X) =
        eqToHom (normalizedLiftZeroObjImage X) ≫
          X.map WalkingParallelPairHom.right ≫
            eqToHom (normalizedLiftOneObjImage X).symm
  normalizedLiftZeroMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      ((normalizedLiftMapDataOfFieldsW1478 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImageOfFieldsW1478 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
          normalizedLiftLeftObjImage normalizedLiftRightObjImage Y)).app WalkingParallelPair.zero =
      (eqToHom (normalizedLiftObjImageOfFieldsW1478 normalizedLiftZeroSrc
        normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
        normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
        normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
        normalizedLiftLeftObjImage normalizedLiftRightObjImage X) ≫ τ).app WalkingParallelPair.zero
  normalizedLiftOneMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      ((normalizedLiftMapDataOfFieldsW1478 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImageOfFieldsW1478 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
          normalizedLiftLeftObjImage normalizedLiftRightObjImage Y)).app WalkingParallelPair.one =
      (eqToHom (normalizedLiftObjImageOfFieldsW1478 normalizedLiftZeroSrc
        normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
        normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
        normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
        normalizedLiftLeftObjImage normalizedLiftRightObjImage X) ≫ τ).app WalkingParallelPair.one
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

/-- W1478 keeps the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1478 builds the W519 provider from its raw closed-embedding field. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding := input.mappedExplicitCokernelClosedEmbedding

/-- W1478 builds the strict-preimage object-data family from its fields. -/
def normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y :=
  fun Y =>
    normalizedLiftObjDataOfFieldsW1478 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac Y

/-- W1478 builds the strict-preimage map-data family from its fields. -/
def normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input Y)
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input Z)
        τ :=
  fun {_Y _Z} τ =>
    normalizedLiftMapDataOfFieldsW1478 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroMap
      input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
      input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
      input.normalizedLiftRightNaturality τ

/-- W1478 derives the raw lift map identity law from zero/one component laws. -/
def normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input (𝟙 Y)).natTrans =
        𝟙 (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input Y).diagram :=
  fun Y => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478,
        normalizedLiftObjDataOfFieldsW1478,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478,
        normalizedLiftMapDataOfFieldsW1478,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapId Y
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478,
        normalizedLiftObjDataOfFieldsW1478,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478,
        normalizedLiftMapDataOfFieldsW1478,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapId Y

/-- W1478 derives the raw lift map composition law from zero/one component laws. -/
def normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input (τ ≫ σ)).natTrans =
        (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input τ).natTrans ≫
          (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
            input σ).natTrans :=
  fun {_Y _Z _T} τ σ => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478,
        normalizedLiftObjDataOfFieldsW1478,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478,
        normalizedLiftMapDataOfFieldsW1478,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapComp τ σ
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478,
        normalizedLiftObjDataOfFieldsW1478,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478,
        normalizedLiftMapDataOfFieldsW1478,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapComp τ σ

/-- W1478 derives the normalized lift object-image law from four components. -/
def normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (normalizedLiftObjDataOfFieldsW1478 input.normalizedLiftZeroSrc
        input.normalizedLiftOneSrc input.normalizedLiftZeroIso
        input.normalizedLiftOneIso input.normalizedLiftLeftSrc
        input.normalizedLiftRightSrc input.normalizedLiftLeftFac
        input.normalizedLiftRightFac
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X :=
  fun X =>
    normalizedLiftObjImageOfFieldsW1478 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroObjImage
      input.normalizedLiftOneObjImage input.normalizedLiftLeftObjImage
      input.normalizedLiftRightObjImage X

/-- W1478 derives the normalized lift map-image law from zero/one components. -/
def normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
      (τ : X ⟶ Y),
      (normalizedLiftMapDataOfFieldsW1478 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
            input Y) =
      eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
            input X) ≫ τ :=
  fun {_X _Y} τ => by
    apply NatTrans.ext
    funext j
    cases j
    · exact input.normalizedLiftZeroMapImage τ
    · exact input.normalizedLiftOneMapImage τ

/-- W1478 builds the raw lift blueprint from its object and functorial fields. -/
def normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData :=
    normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input
  mapData :=
    normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input
  map_id :=
    normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input
  map_comp :=
    normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input

/-- W1478 builds the normalized lift blueprint from the raw lift fields. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input
  obj_image :=
    normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input
  map_image :=
    normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input

/-- W1478 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input

/-- W1478 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1478 builds the W1477 input after reconstructing the map-data family. -/
def w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477 where
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
  normalizedLiftObjImage :=
    normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input
  normalizedLiftZeroMapImage := input.normalizedLiftZeroMapImage
  normalizedLiftOneMapImage := input.normalizedLiftOneMapImage
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

/-- W1478 builds W945 localized-unit data through W1477. -/
def localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input)

/-- W1478 builds W730 boundary/relation data through W1477. -/
def boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input)

/-- W1478 builds W986 target/endpoint data through W1477. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input)

/-- W1478 builds W987 full data through W1477. -/
noncomputable def fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
      input)

/-- W1478's constructed W718 provider keeps the first component field. -/
theorem w1478GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1478's constructed W718 provider keeps the second component field. -/
theorem w1478GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1478's constructed W718 provider keeps the third component field. -/
theorem w1478GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1478's constructed W973 data keeps the constructed W718 provider. -/
theorem w1478ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input :=
  rfl

/-- W1478's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1478ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input :=
  rfl

/-- W1478's constructed W519 provider keeps the raw closed-embedding field. -/
theorem w1478MappedCokernelClosedEmbeddingProviderKeepsRawField
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).isClosedEmbedding f =
      input.mappedExplicitCokernelClosedEmbedding f :=
  rfl

/-- W1478's object-data family keeps the zero object field. -/
theorem w1478NormalizedLiftObjDataKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input Y).zeroSrc =
      input.normalizedLiftZeroSrc Y :=
  rfl

/-- W1478's object-data family keeps the one object field. -/
theorem w1478NormalizedLiftObjDataKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input Y).oneSrc =
      input.normalizedLiftOneSrc Y :=
  rfl

/-- W1478's object-data family keeps the zero comparison isomorphism. -/
theorem w1478NormalizedLiftObjDataKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input Y).zeroIso =
      input.normalizedLiftZeroIso Y :=
  rfl

/-- W1478's object-data family keeps the one comparison isomorphism. -/
theorem w1478NormalizedLiftObjDataKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input Y).oneIso =
      input.normalizedLiftOneIso Y :=
  rfl

/-- W1478's object-data family keeps the left source map. -/
theorem w1478NormalizedLiftObjDataKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input Y).leftSrc =
      input.normalizedLiftLeftSrc Y :=
  rfl

/-- W1478's object-data family keeps the right source map. -/
theorem w1478NormalizedLiftObjDataKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input Y).rightSrc =
      input.normalizedLiftRightSrc Y :=
  rfl

/-- W1478's object-data family keeps the left factorization law. -/
theorem w1478NormalizedLiftObjDataKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input Y).left_fac =
      input.normalizedLiftLeftFac Y :=
  rfl

/-- W1478's object-data family keeps the right factorization law. -/
theorem w1478NormalizedLiftObjDataKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input Y).right_fac =
      input.normalizedLiftRightFac Y :=
  rfl

/-- W1478's map-data family keeps the zero map field. -/
theorem w1478NormalizedLiftMapDataKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input τ).zeroMap =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1478's map-data family keeps the one map field. -/
theorem w1478NormalizedLiftMapDataKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input τ).oneMap =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1478's map-data family keeps the zero-map factorization law. -/
theorem w1478NormalizedLiftMapDataKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input τ).zero_fac =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1478's map-data family keeps the one-map factorization law. -/
theorem w1478NormalizedLiftMapDataKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input τ).one_fac =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1478's map-data family keeps the left naturality law. -/
theorem w1478NormalizedLiftMapDataKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input τ).left_naturality =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1478's map-data family keeps the right naturality law. -/
theorem w1478NormalizedLiftMapDataKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input τ).right_naturality =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1478's raw lift blueprint keeps the constructed object-data family. -/
theorem w1478NormalizedLiftRawBlueprintKeepsConstructedObjData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).objData =
      normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input :=
  rfl

/-- W1478's raw lift blueprint keeps the constructed map-data family. -/
theorem w1478NormalizedLiftRawBlueprintKeepsConstructedMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).mapData τ =
      normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input τ :=
  rfl

/-- W1478's raw lift blueprint keeps the constructed identity law. -/
theorem w1478NormalizedLiftRawBlueprintKeepsMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).map_id Y =
      normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input Y :=
  rfl

/-- W1478's raw lift blueprint keeps the constructed composition law. -/
theorem w1478NormalizedLiftRawBlueprintKeepsMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).map_comp τ σ =
      normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input τ σ :=
  rfl

/-- W1478's normalized lift blueprint keeps the constructed raw lift blueprint. -/
theorem w1478NormalizedLiftBlueprintKeepsConstructedRawBlueprint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).blueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input :=
  rfl

/-- W1478's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1478NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).obj_image X =
      normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input X :=
  rfl

/-- W1478's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1478NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).map_image τ =
      normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input τ :=
  rfl

/-- W1478's input keeps the zero component map-image normalization law. -/
theorem w1478NormalizedLiftMapImageKeepsZeroComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1478 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
            input Y)).app WalkingParallelPair.zero =
      (eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
            input X) ≫ τ).app WalkingParallelPair.zero := by
  simpa [normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478]
    using input.normalizedLiftZeroMapImage τ

/-- W1478's input keeps the one component map-image normalization law. -/
theorem w1478NormalizedLiftMapImageKeepsOneComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1478 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
            input Y)).app WalkingParallelPair.one =
      (eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
            input X) ≫ τ).app WalkingParallelPair.one := by
  simpa [normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478]
    using input.normalizedLiftOneMapImage τ

/-- W1478's W1477 input keeps the first W718 component field. -/
theorem w1478W1477InputKeepsGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).globalClosedEmbeddingPi1 =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1478's W1477 input keeps the second W718 component field. -/
theorem w1478W1477InputKeepsGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).globalClosedEmbeddingPi2 =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1478's W1477 input keeps the third W718 component field. -/
theorem w1478W1477InputKeepsGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).globalClosedEmbeddingPi3 =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1478's W1477 input keeps W519 mapped-cokernel data. -/
theorem w1478W1477InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input :=
  rfl

/-- W1478's W1477 input keeps the zero source object field. -/
theorem w1478W1477InputKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftZeroSrc =
      input.normalizedLiftZeroSrc :=
  rfl

/-- W1478's W1477 input keeps the one source object field. -/
theorem w1478W1477InputKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftOneSrc =
      input.normalizedLiftOneSrc :=
  rfl

/-- W1478's W1477 input keeps the zero comparison isomorphism. -/
theorem w1478W1477InputKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftZeroIso =
      input.normalizedLiftZeroIso :=
  rfl

/-- W1478's W1477 input keeps the one comparison isomorphism. -/
theorem w1478W1477InputKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftOneIso =
      input.normalizedLiftOneIso :=
  rfl

/-- W1478's W1477 input keeps the left source map. -/
theorem w1478W1477InputKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftLeftSrc =
      input.normalizedLiftLeftSrc :=
  rfl

/-- W1478's W1477 input keeps the right source map. -/
theorem w1478W1477InputKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftRightSrc =
      input.normalizedLiftRightSrc :=
  rfl

/-- W1478's W1477 input keeps the left factorization law. -/
theorem w1478W1477InputKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftLeftFac =
      input.normalizedLiftLeftFac :=
  rfl

/-- W1478's W1477 input keeps the right factorization law. -/
theorem w1478W1477InputKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftRightFac =
      input.normalizedLiftRightFac :=
  rfl

/-- W1478's W1477 input keeps the zero map field. -/
theorem w1478W1477InputKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftZeroMap τ =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1478's W1477 input keeps the one map field. -/
theorem w1478W1477InputKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftOneMap τ =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1478's W1477 input keeps the zero-map factorization law. -/
theorem w1478W1477InputKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftZeroMapFac τ =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1478's W1477 input keeps the one-map factorization law. -/
theorem w1478W1477InputKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftOneMapFac τ =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1478's W1477 input keeps the left naturality law. -/
theorem w1478W1477InputKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftLeftNaturality τ =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1478's W1477 input keeps the right naturality law. -/
theorem w1478W1477InputKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftRightNaturality τ =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1478's W1477 input keeps the zero-map identity law. -/
theorem w1478W1477InputKeepsZeroMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftZeroMapId Y =
      input.normalizedLiftZeroMapId Y :=
  rfl

/-- W1478's W1477 input keeps the one-map identity law. -/
theorem w1478W1477InputKeepsOneMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftOneMapId Y =
      input.normalizedLiftOneMapId Y :=
  rfl

/-- W1478's W1477 input keeps the zero-map composition law. -/
theorem w1478W1477InputKeepsZeroMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftZeroMapComp τ σ =
      input.normalizedLiftZeroMapComp τ σ :=
  rfl

/-- W1478's W1477 input keeps the one-map composition law. -/
theorem w1478W1477InputKeepsOneMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftOneMapComp τ σ =
      input.normalizedLiftOneMapComp τ σ :=
  rfl

/-- W1478's W1477 input keeps the object-image normalization field. -/
theorem w1478W1477InputKeepsNormalizedLiftObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftObjImage X =
      normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input X :=
  rfl

/-- W1478's W1477 input keeps the zero-component map-image normalization field. -/
theorem w1478W1477InputKeepsNormalizedLiftZeroMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftZeroMapImage τ =
      input.normalizedLiftZeroMapImage τ :=
  rfl

/-- W1478's W1477 input keeps the one-component map-image normalization field. -/
theorem w1478W1477InputKeepsNormalizedLiftOneMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).normalizedLiftOneMapImage τ =
      input.normalizedLiftOneMapImage τ :=
  rfl

/-- W1478's W1477 input keeps target-difference surjectivity. -/
theorem w1478W1477InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1478's W1477 input keeps target-codomain compact no-univ membership. -/
theorem w1478W1477InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1478's W1477 input keeps the reconstructed localized right adjoint. -/
theorem w1478W1477InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    boundedHomotopyLocalizedRightAdjointOfW1477
        (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1478 input :=
  rfl

/-- W1478's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1478LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1478 input :=
  rfl

/-- W1478's W986 construction keeps the constructed W973 closedness data. -/
theorem w1478TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input :=
  rfl

/-- W1478's constructed W987 provider projects to the constructed W730 data. -/
theorem w1478FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input :=
  rfl

/-- W1478's constructed W987 provider projects to the constructed W986 data. -/
theorem w1478FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478
        input :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputNamesW1478 :
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
    "normalized lift zero object-image normalization",
    "normalized lift one object-image normalization",
    "normalized lift left arrow-image normalization",
    "normalized lift right arrow-image normalization",
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

theorem w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputNamesW1478_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputNamesW1478.length =
      62 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionBundledObjectImageInputNamesW1478 :
    List String :=
  ["normalized lift object-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionBundledObjectImageInputNamesW1478_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionBundledObjectImageInputNamesW1478.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionComponentObjectImageInputNamesW1478 :
    List String :=
  ["normalized lift zero object-image normalization",
    "normalized lift one object-image normalization",
    "normalized lift left arrow-image normalization",
    "normalized lift right arrow-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionComponentObjectImageInputNamesW1478_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionComponentObjectImageInputNamesW1478.length =
      4 :=
  rfl

/-- W1478 replaces one object-image law by four component image laws. -/
theorem w1478BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionSplitsObjectImageInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionBundledObjectImageInputNamesW1478.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionComponentObjectImageInputNamesW1478.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionBundledObjectImageInputNamesW1478_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionComponentObjectImageInputNamesW1478_count]
  decide

/-- W1478 expands the W1477 input count after splitting the object-image law. -/
theorem w1478BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionExpandsW1477InputCount :
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputNamesW1478.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputNamesW1478_count]
  decide

/-- Current W1478 nonterminal strict-preimage object-image construction state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionStateW1478 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  objectImageInputNames : List String
  componentObjectImageInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1478 records the strict-preimage object-image construction path. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionStateW1478 :
    W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionStateW1478 where
  seed :=
    "w1478-w987-boundary-relation-target-strict-preimage-object-image-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputW1478",
      "normalizedLiftObjDataOfFieldsW1478",
      "normalizedLiftMapDataOfFieldsW1478",
      "normalizedLiftObjImageOfFieldsW1478",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "boundedHomotopyLocalizedRightAdjointOfW1478",
      "w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataW1478",
      "w1478GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1478GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1478GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1478ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1478ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1478MappedCokernelClosedEmbeddingProviderKeepsRawField",
      "w1478NormalizedLiftObjDataKeepsZeroSrc",
      "w1478NormalizedLiftObjDataKeepsOneSrc",
      "w1478NormalizedLiftObjDataKeepsZeroIso",
      "w1478NormalizedLiftObjDataKeepsOneIso",
      "w1478NormalizedLiftObjDataKeepsLeftSrc",
      "w1478NormalizedLiftObjDataKeepsRightSrc",
      "w1478NormalizedLiftObjDataKeepsLeftFac",
      "w1478NormalizedLiftObjDataKeepsRightFac",
      "w1478NormalizedLiftMapDataKeepsZeroMap",
      "w1478NormalizedLiftMapDataKeepsOneMap",
      "w1478NormalizedLiftMapDataKeepsZeroMapFac",
      "w1478NormalizedLiftMapDataKeepsOneMapFac",
      "w1478NormalizedLiftMapDataKeepsLeftNaturality",
      "w1478NormalizedLiftMapDataKeepsRightNaturality",
      "w1478NormalizedLiftRawBlueprintKeepsConstructedObjData",
      "w1478NormalizedLiftRawBlueprintKeepsConstructedMapData",
      "w1478NormalizedLiftRawBlueprintKeepsMapId",
      "w1478NormalizedLiftRawBlueprintKeepsMapComp",
      "w1478NormalizedLiftBlueprintKeepsConstructedRawBlueprint",
      "w1478NormalizedLiftBlueprintKeepsObjImage",
      "w1478NormalizedLiftBlueprintKeepsMapImage",
      "w1478NormalizedLiftMapImageKeepsZeroComponent",
      "w1478NormalizedLiftMapImageKeepsOneComponent",
      "w1478W1477InputKeepsGlobalClosedEmbeddingPi1",
      "w1478W1477InputKeepsGlobalClosedEmbeddingPi2",
      "w1478W1477InputKeepsGlobalClosedEmbeddingPi3",
      "w1478W1477InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1478W1477InputKeepsZeroSrc",
      "w1478W1477InputKeepsOneSrc",
      "w1478W1477InputKeepsZeroIso",
      "w1478W1477InputKeepsOneIso",
      "w1478W1477InputKeepsLeftSrc",
      "w1478W1477InputKeepsRightSrc",
      "w1478W1477InputKeepsLeftFac",
      "w1478W1477InputKeepsRightFac",
      "w1478W1477InputKeepsZeroMap",
      "w1478W1477InputKeepsOneMap",
      "w1478W1477InputKeepsZeroMapFac",
      "w1478W1477InputKeepsOneMapFac",
      "w1478W1477InputKeepsLeftNaturality",
      "w1478W1477InputKeepsRightNaturality",
      "w1478W1477InputKeepsZeroMapId",
      "w1478W1477InputKeepsOneMapId",
      "w1478W1477InputKeepsZeroMapComp",
      "w1478W1477InputKeepsOneMapComp",
      "w1478W1477InputKeepsNormalizedLiftObjImage",
      "w1478W1477InputKeepsNormalizedLiftZeroMapImage",
      "w1478W1477InputKeepsNormalizedLiftOneMapImage",
      "w1478W1477InputKeepsTargetDifferenceSurjective",
      "w1478W1477InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1478W1477InputKeepsConstructedLocalizedRightAdjoint",
      "w1478LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1478TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1478FullDataKeepsConstructedBoundaryRelation",
      "w1478FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputNamesW1478_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionBundledObjectImageInputNamesW1478_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionComponentObjectImageInputNamesW1478_count",
      "w1478BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionSplitsObjectImageInput",
      "w1478BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionExpandsW1477InputCount"]
  constructionResult :=
    "proved: W1478 reconstructs the normalized lift object-image law from\
      zero/one object and left/right arrow image laws, then feeds that law\
      into W1477"
  projectionResult :=
    "proved: W1478's derived object-image law is used by the normalized lift\
      blueprint and by the W1477 input while W1477 preserves the map-image,\
      raw lift blueprint, localized-unit, boundary, and target/endpoint\
      projections; product success is still not claimed"
  objectImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionBundledObjectImageInputNamesW1478
  componentObjectImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionComponentObjectImageInputNamesW1478
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputNamesW1478
  productSuccessClaimed := false

theorem currentW1478W987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionStateW1478.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
