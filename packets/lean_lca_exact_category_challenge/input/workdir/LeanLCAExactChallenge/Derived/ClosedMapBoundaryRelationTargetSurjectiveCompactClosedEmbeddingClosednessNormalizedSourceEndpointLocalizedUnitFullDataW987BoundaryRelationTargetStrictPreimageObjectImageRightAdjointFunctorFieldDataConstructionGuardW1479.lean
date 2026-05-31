import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionGuardW1478

/-!
W1479 refines W1478 by constructing the localized right-adjoint functor
from object, morphism, identity, and composition fields while preserving
the W1478 normalized lift object-image split.
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

/-- W1479 assembles one strict-preimage object datum from its constructor fields. -/
def normalizedLiftObjDataOfFieldsW1479
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

/-- W1479 assembles one strict-preimage map datum from its constructor fields. -/
def normalizedLiftMapDataOfFieldsW1479
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
      (normalizedLiftObjDataOfFieldsW1479 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Y)
      (normalizedLiftObjDataOfFieldsW1479 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Z)
      τ where
  zeroMap := zeroMap τ
  oneMap := oneMap τ
  zero_fac := zeroMapFac τ
  one_fac := oneMapFac τ
  left_naturality := leftNaturality τ
  right_naturality := rightNaturality τ

/-- W1479 derives object-image normalization from object and arrow components. -/
def normalizedLiftObjImageOfFieldsW1479
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
    (normalizedLiftObjDataOfFieldsW1479 zeroSrc oneSrc zeroIso oneIso
      leftSrc rightSrc leftFac rightFac
      (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X := by
  refine CategoryTheory.Functor.ext (fun j => ?_) (fun _ _ f => ?_)
  · cases j
    · exact zeroObjImage X
    · exact oneObjImage X
  · cases f
    · simpa [normalizedLiftObjDataOfFieldsW1479,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        leftObjImage X
    · simpa [normalizedLiftObjDataOfFieldsW1479,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        rightObjImage X
    · simp

/-- W1479 packages raw localized right-adjoint functor fields. -/
def localizedRightAdjointFunctorFieldsOfRawW1479
    (obj :
      BoundedHomotopyLocalizedCategoryW1461 →
        BoundedComplexCategory MetrizableLCA.{0})
    (map :
      ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461},
        (X ⟶ Y) → (obj X ⟶ obj Y))
    (mapId :
      ∀ X : BoundedHomotopyLocalizedCategoryW1461,
        map (𝟙 X : X ⟶ X) = 𝟙 (obj X))
    (mapComp :
      ∀ {X Y Z : BoundedHomotopyLocalizedCategoryW1461}
        (f : X ⟶ Y) (g : Y ⟶ Z),
          map (f ≫ g) = map f ≫ map g) :
    LocalizedRightAdjointFunctorFieldsW1467 where
  obj := obj
  map := map
  map_id := mapId
  map_comp := mapComp

/-- W1479 reconstructs the localized right-adjoint functor from raw fields. -/
def localizedRightAdjointOfRawW1479
    (obj :
      BoundedHomotopyLocalizedCategoryW1461 →
        BoundedComplexCategory MetrizableLCA.{0})
    (map :
      ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461},
        (X ⟶ Y) → (obj X ⟶ obj Y))
    (mapId :
      ∀ X : BoundedHomotopyLocalizedCategoryW1461,
        map (𝟙 X : X ⟶ X) = 𝟙 (obj X))
    (mapComp :
      ∀ {X Y Z : BoundedHomotopyLocalizedCategoryW1461}
        (f : X ⟶ Y) (g : Y ⟶ Z),
          map (f ≫ g) = map f ≫ map g) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    (localizedRightAdjointFunctorFieldsOfRawW1479 obj map mapId mapComp)

/--
W1479 keeps W1478's normalized lift object-image split and replaces the
localized right-adjoint functor package by explicit functor fields.
-/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479 :
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
      ((normalizedLiftMapDataOfFieldsW1479 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImageOfFieldsW1479 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
          normalizedLiftLeftObjImage normalizedLiftRightObjImage Y)).app WalkingParallelPair.zero =
      (eqToHom (normalizedLiftObjImageOfFieldsW1479 normalizedLiftZeroSrc
        normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
        normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
        normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
        normalizedLiftLeftObjImage normalizedLiftRightObjImage X) ≫ τ).app WalkingParallelPair.zero
  normalizedLiftOneMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      ((normalizedLiftMapDataOfFieldsW1479 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImageOfFieldsW1479 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
          normalizedLiftLeftObjImage normalizedLiftRightObjImage Y)).app WalkingParallelPair.one =
      (eqToHom (normalizedLiftObjImageOfFieldsW1479 normalizedLiftZeroSrc
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
  boundedHomotopyLocalizedRightAdjointObj :
    BoundedHomotopyLocalizedCategoryW1461 →
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedRightAdjointMap :
    ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461},
      (X ⟶ Y) →
        (boundedHomotopyLocalizedRightAdjointObj X ⟶
          boundedHomotopyLocalizedRightAdjointObj Y)
  boundedHomotopyLocalizedRightAdjointMapId :
    ∀ X : BoundedHomotopyLocalizedCategoryW1461,
      boundedHomotopyLocalizedRightAdjointMap (𝟙 X : X ⟶ X) =
        𝟙 (boundedHomotopyLocalizedRightAdjointObj X)
  boundedHomotopyLocalizedRightAdjointMapComp :
    ∀ {X Y Z : BoundedHomotopyLocalizedCategoryW1461}
      (f : X ⟶ Y) (g : Y ⟶ Z),
        boundedHomotopyLocalizedRightAdjointMap (f ≫ g) =
          boundedHomotopyLocalizedRightAdjointMap f ≫
            boundedHomotopyLocalizedRightAdjointMap g
  boundedHomotopyLocalizedAdjunctionUnitApp :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      X ⟶
        (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
          localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp).obj X
  boundedHomotopyLocalizedAdjunctionUnitNaturality :
    ∀ {X Y : BoundedComplexCategory MetrizableLCA.{0}} (f : X ⟶ Y),
      f ≫ boundedHomotopyLocalizedAdjunctionUnitApp Y =
        boundedHomotopyLocalizedAdjunctionUnitApp X ≫
          (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
            localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp).map f
  boundedHomotopyLocalizedAdjunctionCounitApp :
    ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
      ((localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).obj Y ⟶
        Y
  boundedHomotopyLocalizedAdjunctionCounitNaturality :
    ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y),
      ((localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).map f ≫
          boundedHomotopyLocalizedAdjunctionCounitApp Y =
        boundedHomotopyLocalizedAdjunctionCounitApp X ≫ f
  boundedHomotopyLocalizedAdjunctionLeftTriangleApp :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (localizedAdjunctionLeftTriangleNatTransOfW1467
          (localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
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
          (localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          boundedHomotopyLocalizedAdjunctionUnitApp
          boundedHomotopyLocalizedAdjunctionUnitNaturality
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality).app Y =
        (NatTrans.id
          ((localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp) ⋙
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
          (localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X ⟶
        unitMappingConeModel X
  unitMappingConeIsoInv :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeModel X ⟶
        unitMappingConeIsoSourceW1464
          (localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X
  unitMappingConeIsoHomInvId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoHom X ≫ unitMappingConeIsoInv X =
        𝟙 (unitMappingConeIsoSourceW1464
          (localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfRawW1479
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
            boundedHomotopyLocalizedAdjunctionUnitApp
            boundedHomotopyLocalizedAdjunctionUnitNaturality)
          X)
  unitMappingConeIsoInvHomId :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoInv X ≫ unitMappingConeIsoHom X =
        𝟙 (unitMappingConeModel X)

/-- W1479 keeps the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 := input.globalClosedEmbeddingPi1
  pi2 := input.globalClosedEmbeddingPi2
  pi3 := input.globalClosedEmbeddingPi3

/-- W1479 builds the W519 provider from its raw closed-embedding field. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding := input.mappedExplicitCokernelClosedEmbedding

/-- W1479 builds the strict-preimage object-data family from its fields. -/
def normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y :=
  fun Y =>
    normalizedLiftObjDataOfFieldsW1479 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac Y

/-- W1479 builds the strict-preimage map-data family from its fields. -/
def normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input Y)
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input Z)
        τ :=
  fun {_Y _Z} τ =>
    normalizedLiftMapDataOfFieldsW1479 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroMap
      input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
      input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
      input.normalizedLiftRightNaturality τ

/-- W1479 derives the raw lift map identity law from zero/one component laws. -/
def normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input (𝟙 Y)).natTrans =
        𝟙 (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input Y).diagram :=
  fun Y => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479,
        normalizedLiftObjDataOfFieldsW1479,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479,
        normalizedLiftMapDataOfFieldsW1479,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapId Y
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479,
        normalizedLiftObjDataOfFieldsW1479,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479,
        normalizedLiftMapDataOfFieldsW1479,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapId Y

/-- W1479 derives the raw lift map composition law from zero/one component laws. -/
def normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input (τ ≫ σ)).natTrans =
        (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input τ).natTrans ≫
          (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
            input σ).natTrans :=
  fun {_Y _Z _T} τ σ => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479,
        normalizedLiftObjDataOfFieldsW1479,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479,
        normalizedLiftMapDataOfFieldsW1479,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapComp τ σ
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479,
        normalizedLiftObjDataOfFieldsW1479,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479,
        normalizedLiftMapDataOfFieldsW1479,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapComp τ σ

/-- W1479 derives the normalized lift object-image law from four components. -/
def normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (normalizedLiftObjDataOfFieldsW1479 input.normalizedLiftZeroSrc
        input.normalizedLiftOneSrc input.normalizedLiftZeroIso
        input.normalizedLiftOneIso input.normalizedLiftLeftSrc
        input.normalizedLiftRightSrc input.normalizedLiftLeftFac
        input.normalizedLiftRightFac
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X :=
  fun X =>
    normalizedLiftObjImageOfFieldsW1479 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroObjImage
      input.normalizedLiftOneObjImage input.normalizedLiftLeftObjImage
      input.normalizedLiftRightObjImage X

/-- W1479 derives the normalized lift map-image law from zero/one components. -/
def normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
      (τ : X ⟶ Y),
      (normalizedLiftMapDataOfFieldsW1479 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
            input Y) =
      eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
            input X) ≫ τ :=
  fun {_X _Y} τ => by
    apply NatTrans.ext
    funext j
    cases j
    · exact input.normalizedLiftZeroMapImage τ
    · exact input.normalizedLiftOneMapImage τ

/-- W1479 builds the raw lift blueprint from its object and functorial fields. -/
def normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData :=
    normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input
  mapData :=
    normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input
  map_id :=
    normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input
  map_comp :=
    normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input

/-- W1479 builds the normalized lift blueprint from the raw lift fields. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input
  obj_image :=
    normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input
  map_image :=
    normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input

/-- W1479 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input

/-- W1479 reconstructs the localized right-adjoint functor fields. -/
def boundedHomotopyLocalizedRightAdjointFieldsOfW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    LocalizedRightAdjointFunctorFieldsW1467 :=
  localizedRightAdjointFunctorFieldsOfRawW1479
    input.boundedHomotopyLocalizedRightAdjointObj
    input.boundedHomotopyLocalizedRightAdjointMap
    input.boundedHomotopyLocalizedRightAdjointMapId
    input.boundedHomotopyLocalizedRightAdjointMapComp

/-- W1479 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    (boundedHomotopyLocalizedRightAdjointFieldsOfW1479 input)

/-- W1479's reconstructed right-adjoint field package keeps the object map. -/
theorem w1479LocalizedRightAdjointFieldsKeepObj
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (X : BoundedHomotopyLocalizedCategoryW1461) :
    (boundedHomotopyLocalizedRightAdjointFieldsOfW1479 input).obj X =
      input.boundedHomotopyLocalizedRightAdjointObj X :=
  rfl

/-- W1479's reconstructed right-adjoint field package keeps the morphism map. -/
theorem w1479LocalizedRightAdjointFieldsKeepMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y) :
    (boundedHomotopyLocalizedRightAdjointFieldsOfW1479 input).map f =
      input.boundedHomotopyLocalizedRightAdjointMap f :=
  rfl

/-- W1479's reconstructed right adjoint keeps the object map. -/
theorem w1479LocalizedRightAdjointKeepsObj
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (X : BoundedHomotopyLocalizedCategoryW1461) :
    (boundedHomotopyLocalizedRightAdjointOfW1479 input).obj X =
      input.boundedHomotopyLocalizedRightAdjointObj X :=
  rfl

/-- W1479's reconstructed right adjoint keeps the morphism map. -/
theorem w1479LocalizedRightAdjointKeepsMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y) :
    (boundedHomotopyLocalizedRightAdjointOfW1479 input).map f =
      input.boundedHomotopyLocalizedRightAdjointMap f :=
  rfl

/-- W1479 builds the W1477 input after reconstructing the map-data family. -/
def w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
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
    normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
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
    boundedHomotopyLocalizedRightAdjointFieldsOfW1479 input
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

/-- W1479 builds W945 localized-unit data through W1477. -/
def localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input)

/-- W1479 builds W730 boundary/relation data through W1477. -/
def boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input)

/-- W1479 builds W986 target/endpoint data through W1477. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input)

/-- W1479 builds W987 full data through W1477. -/
noncomputable def fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
      input)

/-- W1479's constructed W718 provider keeps the first component field. -/
theorem w1479GlobalClosedEmbeddingComponentsKeepsPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1479's constructed W718 provider keeps the second component field. -/
theorem w1479GlobalClosedEmbeddingComponentsKeepsPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1479's constructed W718 provider keeps the third component field. -/
theorem w1479GlobalClosedEmbeddingComponentsKeepsPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1479's constructed W973 data keeps the constructed W718 provider. -/
theorem w1479ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input :=
  rfl

/-- W1479's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1479ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input :=
  rfl

/-- W1479's constructed W519 provider keeps the raw closed-embedding field. -/
theorem w1479MappedCokernelClosedEmbeddingProviderKeepsRawField
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).isClosedEmbedding f =
      input.mappedExplicitCokernelClosedEmbedding f :=
  rfl

/-- W1479's object-data family keeps the zero object field. -/
theorem w1479NormalizedLiftObjDataKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input Y).zeroSrc =
      input.normalizedLiftZeroSrc Y :=
  rfl

/-- W1479's object-data family keeps the one object field. -/
theorem w1479NormalizedLiftObjDataKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input Y).oneSrc =
      input.normalizedLiftOneSrc Y :=
  rfl

/-- W1479's object-data family keeps the zero comparison isomorphism. -/
theorem w1479NormalizedLiftObjDataKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input Y).zeroIso =
      input.normalizedLiftZeroIso Y :=
  rfl

/-- W1479's object-data family keeps the one comparison isomorphism. -/
theorem w1479NormalizedLiftObjDataKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input Y).oneIso =
      input.normalizedLiftOneIso Y :=
  rfl

/-- W1479's object-data family keeps the left source map. -/
theorem w1479NormalizedLiftObjDataKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input Y).leftSrc =
      input.normalizedLiftLeftSrc Y :=
  rfl

/-- W1479's object-data family keeps the right source map. -/
theorem w1479NormalizedLiftObjDataKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input Y).rightSrc =
      input.normalizedLiftRightSrc Y :=
  rfl

/-- W1479's object-data family keeps the left factorization law. -/
theorem w1479NormalizedLiftObjDataKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input Y).left_fac =
      input.normalizedLiftLeftFac Y :=
  rfl

/-- W1479's object-data family keeps the right factorization law. -/
theorem w1479NormalizedLiftObjDataKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input Y).right_fac =
      input.normalizedLiftRightFac Y :=
  rfl

/-- W1479's map-data family keeps the zero map field. -/
theorem w1479NormalizedLiftMapDataKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input τ).zeroMap =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1479's map-data family keeps the one map field. -/
theorem w1479NormalizedLiftMapDataKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input τ).oneMap =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1479's map-data family keeps the zero-map factorization law. -/
theorem w1479NormalizedLiftMapDataKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input τ).zero_fac =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1479's map-data family keeps the one-map factorization law. -/
theorem w1479NormalizedLiftMapDataKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input τ).one_fac =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1479's map-data family keeps the left naturality law. -/
theorem w1479NormalizedLiftMapDataKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input τ).left_naturality =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1479's map-data family keeps the right naturality law. -/
theorem w1479NormalizedLiftMapDataKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input τ).right_naturality =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1479's raw lift blueprint keeps the constructed object-data family. -/
theorem w1479NormalizedLiftRawBlueprintKeepsConstructedObjData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).objData =
      normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input :=
  rfl

/-- W1479's raw lift blueprint keeps the constructed map-data family. -/
theorem w1479NormalizedLiftRawBlueprintKeepsConstructedMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).mapData τ =
      normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input τ :=
  rfl

/-- W1479's raw lift blueprint keeps the constructed identity law. -/
theorem w1479NormalizedLiftRawBlueprintKeepsMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).map_id Y =
      normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input Y :=
  rfl

/-- W1479's raw lift blueprint keeps the constructed composition law. -/
theorem w1479NormalizedLiftRawBlueprintKeepsMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).map_comp τ σ =
      normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input τ σ :=
  rfl

/-- W1479's normalized lift blueprint keeps the constructed raw lift blueprint. -/
theorem w1479NormalizedLiftBlueprintKeepsConstructedRawBlueprint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).blueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input :=
  rfl

/-- W1479's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1479NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).obj_image X =
      normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input X :=
  rfl

/-- W1479's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1479NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).map_image τ =
      normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input τ :=
  rfl

/-- W1479's input keeps the zero component map-image normalization law. -/
theorem w1479NormalizedLiftMapImageKeepsZeroComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1479 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
            input Y)).app WalkingParallelPair.zero =
      (eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
            input X) ≫ τ).app WalkingParallelPair.zero := by
  simpa [normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479]
    using input.normalizedLiftZeroMapImage τ

/-- W1479's input keeps the one component map-image normalization law. -/
theorem w1479NormalizedLiftMapImageKeepsOneComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1479 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
            input Y)).app WalkingParallelPair.one =
      (eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
            input X) ≫ τ).app WalkingParallelPair.one := by
  simpa [normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479]
    using input.normalizedLiftOneMapImage τ

/-- W1479's W1477 input keeps the first W718 component field. -/
theorem w1479W1477InputKeepsGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).globalClosedEmbeddingPi1 =
      input.globalClosedEmbeddingPi1 :=
  rfl

/-- W1479's W1477 input keeps the second W718 component field. -/
theorem w1479W1477InputKeepsGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).globalClosedEmbeddingPi2 =
      input.globalClosedEmbeddingPi2 :=
  rfl

/-- W1479's W1477 input keeps the third W718 component field. -/
theorem w1479W1477InputKeepsGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).globalClosedEmbeddingPi3 =
      input.globalClosedEmbeddingPi3 :=
  rfl

/-- W1479's W1477 input keeps W519 mapped-cokernel data. -/
theorem w1479W1477InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input :=
  rfl

/-- W1479's W1477 input keeps the zero source object field. -/
theorem w1479W1477InputKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftZeroSrc =
      input.normalizedLiftZeroSrc :=
  rfl

/-- W1479's W1477 input keeps the one source object field. -/
theorem w1479W1477InputKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftOneSrc =
      input.normalizedLiftOneSrc :=
  rfl

/-- W1479's W1477 input keeps the zero comparison isomorphism. -/
theorem w1479W1477InputKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftZeroIso =
      input.normalizedLiftZeroIso :=
  rfl

/-- W1479's W1477 input keeps the one comparison isomorphism. -/
theorem w1479W1477InputKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftOneIso =
      input.normalizedLiftOneIso :=
  rfl

/-- W1479's W1477 input keeps the left source map. -/
theorem w1479W1477InputKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftLeftSrc =
      input.normalizedLiftLeftSrc :=
  rfl

/-- W1479's W1477 input keeps the right source map. -/
theorem w1479W1477InputKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftRightSrc =
      input.normalizedLiftRightSrc :=
  rfl

/-- W1479's W1477 input keeps the left factorization law. -/
theorem w1479W1477InputKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftLeftFac =
      input.normalizedLiftLeftFac :=
  rfl

/-- W1479's W1477 input keeps the right factorization law. -/
theorem w1479W1477InputKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftRightFac =
      input.normalizedLiftRightFac :=
  rfl

/-- W1479's W1477 input keeps the zero map field. -/
theorem w1479W1477InputKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftZeroMap τ =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1479's W1477 input keeps the one map field. -/
theorem w1479W1477InputKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftOneMap τ =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1479's W1477 input keeps the zero-map factorization law. -/
theorem w1479W1477InputKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftZeroMapFac τ =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1479's W1477 input keeps the one-map factorization law. -/
theorem w1479W1477InputKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftOneMapFac τ =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1479's W1477 input keeps the left naturality law. -/
theorem w1479W1477InputKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftLeftNaturality τ =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1479's W1477 input keeps the right naturality law. -/
theorem w1479W1477InputKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftRightNaturality τ =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1479's W1477 input keeps the zero-map identity law. -/
theorem w1479W1477InputKeepsZeroMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftZeroMapId Y =
      input.normalizedLiftZeroMapId Y :=
  rfl

/-- W1479's W1477 input keeps the one-map identity law. -/
theorem w1479W1477InputKeepsOneMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftOneMapId Y =
      input.normalizedLiftOneMapId Y :=
  rfl

/-- W1479's W1477 input keeps the zero-map composition law. -/
theorem w1479W1477InputKeepsZeroMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftZeroMapComp τ σ =
      input.normalizedLiftZeroMapComp τ σ :=
  rfl

/-- W1479's W1477 input keeps the one-map composition law. -/
theorem w1479W1477InputKeepsOneMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftOneMapComp τ σ =
      input.normalizedLiftOneMapComp τ σ :=
  rfl

/-- W1479's W1477 input keeps the object-image normalization field. -/
theorem w1479W1477InputKeepsNormalizedLiftObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftObjImage X =
      normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input X :=
  rfl

/-- W1479's W1477 input keeps the zero-component map-image normalization field. -/
theorem w1479W1477InputKeepsNormalizedLiftZeroMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftZeroMapImage τ =
      input.normalizedLiftZeroMapImage τ :=
  rfl

/-- W1479's W1477 input keeps the one-component map-image normalization field. -/
theorem w1479W1477InputKeepsNormalizedLiftOneMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).normalizedLiftOneMapImage τ =
      input.normalizedLiftOneMapImage τ :=
  rfl

/-- W1479's W1477 input keeps target-difference surjectivity. -/
theorem w1479W1477InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1479's W1477 input keeps target-codomain compact no-univ membership. -/
theorem w1479W1477InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1479's W1477 input keeps the reconstructed localized right adjoint. -/
theorem w1479W1477InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    boundedHomotopyLocalizedRightAdjointOfW1477
        (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1479 input :=
  rfl

/-- W1479's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1479LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1479 input :=
  rfl

/-- W1479's W986 construction keeps the constructed W973 closedness data. -/
theorem w1479TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input :=
  rfl

/-- W1479's constructed W987 provider projects to the constructed W730 data. -/
theorem w1479FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input :=
  rfl

/-- W1479's constructed W987 provider projects to the constructed W986 data. -/
theorem w1479FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479
        input :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputNamesW1479 :
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

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputNamesW1479_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputNamesW1479.length =
      62 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledObjectImageInputNamesW1479 :
    List String :=
  ["normalized lift object-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledObjectImageInputNamesW1479_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledObjectImageInputNamesW1479.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentObjectImageInputNamesW1479 :
    List String :=
  ["normalized lift zero object-image normalization",
    "normalized lift one object-image normalization",
    "normalized lift left arrow-image normalization",
    "normalized lift right arrow-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentObjectImageInputNamesW1479_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentObjectImageInputNamesW1479.length =
      4 :=
  rfl

/-- W1479 replaces one object-image law by four component image laws. -/
theorem w1479BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionSplitsObjectImageInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledObjectImageInputNamesW1479.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentObjectImageInputNamesW1479.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledObjectImageInputNamesW1479_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentObjectImageInputNamesW1479_count]
  decide

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledRightAdjointInputNamesW1479 :
    List String :=
  ["bounded homotopy localized right-adjoint functor field package"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledRightAdjointInputNamesW1479_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledRightAdjointInputNamesW1479.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentRightAdjointInputNamesW1479 :
    List String :=
  ["bounded homotopy localized right-adjoint object map",
    "bounded homotopy localized right-adjoint morphism map",
    "bounded homotopy localized right-adjoint identity law",
    "bounded homotopy localized right-adjoint composition law"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentRightAdjointInputNamesW1479_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentRightAdjointInputNamesW1479.length =
      4 :=
  rfl

/-- W1479 replaces one right-adjoint functor package by four functor fields. -/
theorem w1479BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionSplitsRightAdjointInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledRightAdjointInputNamesW1479.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentRightAdjointInputNamesW1479.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledRightAdjointInputNamesW1479_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentRightAdjointInputNamesW1479_count]
  decide

/-- W1479 makes W1478's conceptual right-adjoint split explicit as constructor fields. -/
theorem w1479BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionKeepsW1478ConceptualInputCount :
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputNamesW1478.length =
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputNamesW1479.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageFieldDataConstructionInputNamesW1478_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputNamesW1479_count]

/-- W1479 expands the W1477 input count after splitting the object-image law. -/
theorem w1479BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionExpandsW1477InputCount :
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputNamesW1479.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputNamesW1479_count]
  decide

/-- Current W1479 nonterminal strict-preimage object-image right-adjoint functor construction state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionStateW1479 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  objectImageInputNames : List String
  componentObjectImageInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1479 records the strict-preimage object-image right-adjoint functor construction path. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionStateW1479 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionStateW1479 where
  seed :=
    "w1479-w987-boundary-relation-target-strict-preimage-object-image-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputW1479",
      "normalizedLiftObjDataOfFieldsW1479",
      "normalizedLiftMapDataOfFieldsW1479",
      "normalizedLiftObjImageOfFieldsW1479",
      "localizedRightAdjointFunctorFieldsOfRawW1479",
      "localizedRightAdjointOfRawW1479",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "boundedHomotopyLocalizedRightAdjointFieldsOfW1479",
      "boundedHomotopyLocalizedRightAdjointOfW1479",
      "w1479LocalizedRightAdjointFieldsKeepObj",
      "w1479LocalizedRightAdjointFieldsKeepMap",
      "w1479LocalizedRightAdjointKeepsObj",
      "w1479LocalizedRightAdjointKeepsMap",
      "w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataW1479",
      "w1479GlobalClosedEmbeddingComponentsKeepsPi1",
      "w1479GlobalClosedEmbeddingComponentsKeepsPi2",
      "w1479GlobalClosedEmbeddingComponentsKeepsPi3",
      "w1479ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1479ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1479MappedCokernelClosedEmbeddingProviderKeepsRawField",
      "w1479NormalizedLiftObjDataKeepsZeroSrc",
      "w1479NormalizedLiftObjDataKeepsOneSrc",
      "w1479NormalizedLiftObjDataKeepsZeroIso",
      "w1479NormalizedLiftObjDataKeepsOneIso",
      "w1479NormalizedLiftObjDataKeepsLeftSrc",
      "w1479NormalizedLiftObjDataKeepsRightSrc",
      "w1479NormalizedLiftObjDataKeepsLeftFac",
      "w1479NormalizedLiftObjDataKeepsRightFac",
      "w1479NormalizedLiftMapDataKeepsZeroMap",
      "w1479NormalizedLiftMapDataKeepsOneMap",
      "w1479NormalizedLiftMapDataKeepsZeroMapFac",
      "w1479NormalizedLiftMapDataKeepsOneMapFac",
      "w1479NormalizedLiftMapDataKeepsLeftNaturality",
      "w1479NormalizedLiftMapDataKeepsRightNaturality",
      "w1479NormalizedLiftRawBlueprintKeepsConstructedObjData",
      "w1479NormalizedLiftRawBlueprintKeepsConstructedMapData",
      "w1479NormalizedLiftRawBlueprintKeepsMapId",
      "w1479NormalizedLiftRawBlueprintKeepsMapComp",
      "w1479NormalizedLiftBlueprintKeepsConstructedRawBlueprint",
      "w1479NormalizedLiftBlueprintKeepsObjImage",
      "w1479NormalizedLiftBlueprintKeepsMapImage",
      "w1479NormalizedLiftMapImageKeepsZeroComponent",
      "w1479NormalizedLiftMapImageKeepsOneComponent",
      "w1479W1477InputKeepsGlobalClosedEmbeddingPi1",
      "w1479W1477InputKeepsGlobalClosedEmbeddingPi2",
      "w1479W1477InputKeepsGlobalClosedEmbeddingPi3",
      "w1479W1477InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1479W1477InputKeepsZeroSrc",
      "w1479W1477InputKeepsOneSrc",
      "w1479W1477InputKeepsZeroIso",
      "w1479W1477InputKeepsOneIso",
      "w1479W1477InputKeepsLeftSrc",
      "w1479W1477InputKeepsRightSrc",
      "w1479W1477InputKeepsLeftFac",
      "w1479W1477InputKeepsRightFac",
      "w1479W1477InputKeepsZeroMap",
      "w1479W1477InputKeepsOneMap",
      "w1479W1477InputKeepsZeroMapFac",
      "w1479W1477InputKeepsOneMapFac",
      "w1479W1477InputKeepsLeftNaturality",
      "w1479W1477InputKeepsRightNaturality",
      "w1479W1477InputKeepsZeroMapId",
      "w1479W1477InputKeepsOneMapId",
      "w1479W1477InputKeepsZeroMapComp",
      "w1479W1477InputKeepsOneMapComp",
      "w1479W1477InputKeepsNormalizedLiftObjImage",
      "w1479W1477InputKeepsNormalizedLiftZeroMapImage",
      "w1479W1477InputKeepsNormalizedLiftOneMapImage",
      "w1479W1477InputKeepsTargetDifferenceSurjective",
      "w1479W1477InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1479W1477InputKeepsConstructedLocalizedRightAdjoint",
      "w1479LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1479TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1479FullDataKeepsConstructedBoundaryRelation",
      "w1479FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputNamesW1479_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledObjectImageInputNamesW1479_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentObjectImageInputNamesW1479_count",
      "w1479BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionSplitsObjectImageInput",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledRightAdjointInputNamesW1479_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentRightAdjointInputNamesW1479_count",
      "w1479BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionSplitsRightAdjointInput",
      "w1479BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionKeepsW1478ConceptualInputCount",
      "w1479BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionExpandsW1477InputCount"]
  constructionResult :=
    "proved: W1479 reconstructs the normalized lift object-image law and\
      the localized right-adjoint functor fields, then feeds those laws\
      into W1477"
  projectionResult :=
    "proved: W1479's derived object-image law is used by the normalized lift\
      blueprint and its derived localized right adjoint is used by the W1477\
      input while W1477 preserves the map-image, raw lift blueprint,\
      localized-unit, boundary, and target/endpoint projections; product\
      success is still not claimed"
  objectImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionBundledObjectImageInputNamesW1479
  componentObjectImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionComponentObjectImageInputNamesW1479
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionInputNamesW1479
  productSuccessClaimed := false

theorem currentW1479W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorFieldDataConstructionStateW1479.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
