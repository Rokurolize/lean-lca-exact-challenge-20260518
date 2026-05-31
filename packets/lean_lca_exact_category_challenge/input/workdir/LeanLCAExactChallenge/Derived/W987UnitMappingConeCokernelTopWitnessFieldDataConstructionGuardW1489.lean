import LeanLCAExactChallenge.Derived.W987UnitMappingConeKernelEqualityFieldDataConstructionGuardW1488

/-!
W1489 refines W1488 by constructing the unit mapping-cone cokernel-top family
from surjectivity witness fields, while preserving the unit mapping-cone
kernel-equality, closed-embedding, endpoint, selected-difference,
mapped-cokernel, target-surjectivity, target-compactness, right-adjoint, and
object-image splits.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1489 assembles one strict-preimage object datum from its constructor fields. -/
def normalizedLiftObjDataOfFieldsW1489
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

/-- W1489 assembles one strict-preimage map datum from its constructor fields. -/
def normalizedLiftMapDataOfFieldsW1489
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
      (normalizedLiftObjDataOfFieldsW1489 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Y)
      (normalizedLiftObjDataOfFieldsW1489 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Z)
      τ where
  zeroMap := zeroMap τ
  oneMap := oneMap τ
  zero_fac := zeroMapFac τ
  one_fac := oneMapFac τ
  left_naturality := leftNaturality τ
  right_naturality := rightNaturality τ

/-- W1489 derives object-image normalization from object and arrow components. -/
def normalizedLiftObjImageOfFieldsW1489
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
    (normalizedLiftObjDataOfFieldsW1489 zeroSrc oneSrc zeroIso oneIso
      leftSrc rightSrc leftFac rightFac
      (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X := by
  refine CategoryTheory.Functor.ext (fun j => ?_) (fun _ _ f => ?_)
  · cases j
    · exact zeroObjImage X
    · exact oneObjImage X
  · cases f
    · simpa [normalizedLiftObjDataOfFieldsW1489,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        leftObjImage X
    · simpa [normalizedLiftObjDataOfFieldsW1489,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        rightObjImage X
    · simp

/-- W1489 packages raw localized right-adjoint functor fields. -/
def localizedRightAdjointFunctorFieldsOfRawW1489
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

/-- W1489 reconstructs the localized right-adjoint functor from raw fields. -/
def localizedRightAdjointOfRawW1489
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
    (localizedRightAdjointFunctorFieldsOfRawW1489 obj map mapId mapComp)

/-- W1489 builds target-difference surjectivity from a preimage chooser. -/
def targetDifferenceSurjectivePrimitiveOfWitnessW1489
    (targetDifferenceSurjectivePreimage :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (_y : wppOpCodomainW441 Y),
          wppOpDomainW441 Y)
    (targetDifferenceSurjectivePreimageSpec :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (y : wppOpCodomainW441 Y),
          (((wppOpLeftW441 Y - wppOpRightW441 Y) :
            wppOpDomainW441 Y ⟶ wppOpCodomainW441 Y) :
            wppOpDomainW441 Y → wppOpCodomainW441 Y)
            (targetDifferenceSurjectivePreimage Y y) = y)
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    targetDifferenceSurjectivePrimitiveW923 Y :=
  fun y =>
    ⟨targetDifferenceSurjectivePreimage Y y,
      targetDifferenceSurjectivePreimageSpec Y y⟩

/-- W1489 builds target-codomain compact no-univ membership from point witnesses. -/
def targetCodomainCompactNoUnivMembershipPrimitiveOfWitnessW1489
    (targetCodomainCompactMeetPoint :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        {f : Filter (wppOpCodomainW441 Y)},
          f ≠ ⊥ → wppOpCodomainW441 Y)
    (targetCodomainCompactMeetSpec :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        {f : Filter (wppOpCodomainW441 Y)} (hf : f ≠ ⊥),
          (𝓝 (targetCodomainCompactMeetPoint Y (f := f) hf) ⊓ f) ≠ ⊥)
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    targetCodomainCompactNoUnivMembershipPrimitiveW930 Y :=
  fun {f} hf =>
    ⟨targetCodomainCompactMeetPoint Y (f := f) hf,
      targetCodomainCompactMeetSpec Y (f := f) hf⟩

/-- W1489 builds mapped explicit cokernel closed embeddings from component fields. -/
def mappedExplicitCokernelClosedEmbeddingOfFieldsW1489
    (mappedExplicitCokernelEmbedding :
      ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
        IsEmbedding (f : X → Y))
    (mappedExplicitCokernelClosedRange :
      ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
        IsClosed (Set.range (f : X → Y)))
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    IsClosedEmbedding (f : X → Y) :=
  IsClosedEmbedding.mk
    (mappedExplicitCokernelEmbedding f)
    (mappedExplicitCokernelClosedRange f)

/-- W1489 builds endpoint closed embeddings from endpoint embedding and closed-range fields. -/
def endpointClosedEmbeddingOfFieldsW1489
    (endpointEmbedding :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
        IsEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂))
    (endpointClosedRange :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
        IsClosed
          (Set.range ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)))
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂) :=
  IsClosedEmbedding.mk
    (endpointEmbedding K i)
    (endpointClosedRange K i)

/-- W1489 builds unit mapping-cone closed embeddings from component fields. -/
def unitMappingConeClosedEmbeddingOfFieldsW1489
    (unitMappingConeModel : UnitMappingConeModelW962)
    (unitMappingConeEmbedding :
      ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
        IsEmbedding (((unitMappingConeModel X).as.sc i).f :
          ((unitMappingConeModel X).as.sc i).X₁ →
            ((unitMappingConeModel X).as.sc i).X₂))
    (unitMappingConeClosedRange :
      ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
        IsClosed
          (Set.range (((unitMappingConeModel X).as.sc i).f :
            ((unitMappingConeModel X).as.sc i).X₁ →
              ((unitMappingConeModel X).as.sc i).X₂)))
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    IsClosedEmbedding (((unitMappingConeModel X).as.sc i).f :
      ((unitMappingConeModel X).as.sc i).X₁ →
        ((unitMappingConeModel X).as.sc i).X₂) :=
  IsClosedEmbedding.mk
    (unitMappingConeEmbedding X i)
    (unitMappingConeClosedRange X i)

/-- W1489 builds unit mapping-cone cokernel-top facts from surjectivity witnesses. -/
def unitMappingConeCokernelTopOfWitnessW1489
    (unitMappingConeModel : UnitMappingConeModelW962)
    (unitMappingConeCokernelPreimage :
      ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
        ((unitMappingConeModel X).as.sc i).X₃ →
          ((unitMappingConeModel X).as.sc i).X₂)
    (unitMappingConeCokernelPreimage_eq :
      ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
        (x₃ : ((unitMappingConeModel X).as.sc i).X₃),
          ((unitMappingConeModel X).as.sc i).g
              (unitMappingConeCokernelPreimage X i x₃) =
            x₃)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    MetrizableLCA.cokernelSubgroup (((unitMappingConeModel X).as.sc i).g) =
      ⊤ :=
  MetrizableLCA.cokernelSubgroup_eq_top_of_surjective
    (((unitMappingConeModel X).as.sc i).g) (by
      intro x₃
      exact ⟨unitMappingConeCokernelPreimage X i x₃,
        unitMappingConeCokernelPreimage_eq X i x₃⟩)

/-- W1489 builds unit mapping-cone kernel equalities from implication fields. -/
def unitMappingConeKernelEqualityOfFieldsW1489
    (unitMappingConeModel : UnitMappingConeModelW962)
    (unitMappingConeKernelForward :
      ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
        (x₂ : ((unitMappingConeModel X).as.sc i).X₂),
          ((unitMappingConeModel X).as.sc i).g x₂ = 0 →
            ∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
              ((unitMappingConeModel X).as.sc i).f x₁ = x₂)
    (unitMappingConeKernelBackward :
      ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
        (x₂ : ((unitMappingConeModel X).as.sc i).X₂),
          (∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
              ((unitMappingConeModel X).as.sc i).f x₁ = x₂) →
            ((unitMappingConeModel X).as.sc i).g x₂ = 0)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
    (x₂ : ((unitMappingConeModel X).as.sc i).X₂) :
    ((unitMappingConeModel X).as.sc i).g x₂ = 0 ↔
      ∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
        ((unitMappingConeModel X).as.sc i).f x₁ = x₂ :=
  ⟨unitMappingConeKernelForward X i x₂,
    unitMappingConeKernelBackward X i x₂⟩

/-- W1489 builds the first selected-difference closed-embedding field from components. -/
def selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1489
    (globalClosedEmbeddingPi1Embedding :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
        IsEmbedding
          (selectedMetrizableDifferenceπ₁W481 S :
            (S.obj ordinarySourceIndexW484).X₁ →
              (S.obj ordinaryTargetIndexW484).X₁))
    (globalClosedEmbeddingPi1ClosedRange :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
        IsClosed
          (Set.range
            (selectedMetrizableDifferenceπ₁W481 S :
              (S.obj ordinarySourceIndexW484).X₁ →
                (S.obj ordinaryTargetIndexW484).X₁))) :
    SelectedDifferenceClosedEmbeddingPi1DiagramFieldW714 :=
  fun S =>
    IsClosedEmbedding.mk
      (globalClosedEmbeddingPi1Embedding S)
      (globalClosedEmbeddingPi1ClosedRange S)

/-- W1489 builds the second selected-difference closed-embedding field from components. -/
def selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1489
    (globalClosedEmbeddingPi2Embedding :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
        IsEmbedding
          (selectedMetrizableDifferenceπ₂W481 S :
            (S.obj ordinarySourceIndexW484).X₂ →
              (S.obj ordinaryTargetIndexW484).X₂))
    (globalClosedEmbeddingPi2ClosedRange :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
        IsClosed
          (Set.range
            (selectedMetrizableDifferenceπ₂W481 S :
              (S.obj ordinarySourceIndexW484).X₂ →
                (S.obj ordinaryTargetIndexW484).X₂))) :
    SelectedDifferenceClosedEmbeddingPi2DiagramFieldW714 :=
  fun S =>
    IsClosedEmbedding.mk
      (globalClosedEmbeddingPi2Embedding S)
      (globalClosedEmbeddingPi2ClosedRange S)

/-- W1489 builds the third selected-difference closed-embedding field from components. -/
def selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1489
    (globalClosedEmbeddingPi3Embedding :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
        IsEmbedding
          (selectedMetrizableDifferenceπ₃W481 S :
            (S.obj ordinarySourceIndexW484).X₃ →
              (S.obj ordinaryTargetIndexW484).X₃))
    (globalClosedEmbeddingPi3ClosedRange :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
        IsClosed
          (Set.range
            (selectedMetrizableDifferenceπ₃W481 S :
              (S.obj ordinarySourceIndexW484).X₃ →
                (S.obj ordinaryTargetIndexW484).X₃))) :
    SelectedDifferenceClosedEmbeddingPi3DiagramFieldW714 :=
  fun S =>
    IsClosedEmbedding.mk
      (globalClosedEmbeddingPi3Embedding S)
      (globalClosedEmbeddingPi3ClosedRange S)

/--
W1489 keeps W1488's unit mapping-cone kernel-equality, closed-embedding,
endpoint, selected-difference, mapped-cokernel, target-surjectivity,
target-compactness, normalized lift, and localized right-adjoint splits and
replaces the unit mapping-cone cokernel-top family by preimage witness fields.
-/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489 :
    Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationPullbackProvider :
    ClosedNatTransOrdinaryRelationPullbackProviderW712
  targetRelationLiftsProvider :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
  targetDifferenceSurjectivePreimage :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
      (_y : wppOpCodomainW441 Y),
        wppOpDomainW441 Y
  targetDifferenceSurjectivePreimageSpec :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
      (y : wppOpCodomainW441 Y),
        (((wppOpLeftW441 Y - wppOpRightW441 Y) :
          wppOpDomainW441 Y ⟶ wppOpCodomainW441 Y) :
          wppOpDomainW441 Y → wppOpCodomainW441 Y)
          (targetDifferenceSurjectivePreimage Y y) = y
  targetCodomainCompactMeetPoint :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
      {f : Filter (wppOpCodomainW441 Y)},
        f ≠ ⊥ → wppOpCodomainW441 Y
  targetCodomainCompactMeetSpec :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
      {f : Filter (wppOpCodomainW441 Y)} (hf : f ≠ ⊥),
        (𝓝 (targetCodomainCompactMeetPoint Y (f := f) hf) ⊓ f) ≠ ⊥
  globalClosedEmbeddingPi1Embedding :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      IsEmbedding
        (selectedMetrizableDifferenceπ₁W481 S :
          (S.obj ordinarySourceIndexW484).X₁ →
            (S.obj ordinaryTargetIndexW484).X₁)
  globalClosedEmbeddingPi1ClosedRange :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      IsClosed
        (Set.range
          (selectedMetrizableDifferenceπ₁W481 S :
            (S.obj ordinarySourceIndexW484).X₁ →
              (S.obj ordinaryTargetIndexW484).X₁))
  globalClosedEmbeddingPi2Embedding :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      IsEmbedding
        (selectedMetrizableDifferenceπ₂W481 S :
          (S.obj ordinarySourceIndexW484).X₂ →
            (S.obj ordinaryTargetIndexW484).X₂)
  globalClosedEmbeddingPi2ClosedRange :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      IsClosed
        (Set.range
          (selectedMetrizableDifferenceπ₂W481 S :
            (S.obj ordinarySourceIndexW484).X₂ →
              (S.obj ordinaryTargetIndexW484).X₂))
  globalClosedEmbeddingPi3Embedding :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      IsEmbedding
        (selectedMetrizableDifferenceπ₃W481 S :
          (S.obj ordinarySourceIndexW484).X₃ →
            (S.obj ordinaryTargetIndexW484).X₃)
  globalClosedEmbeddingPi3ClosedRange :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      IsClosed
        (Set.range
          (selectedMetrizableDifferenceπ₃W481 S :
            (S.obj ordinarySourceIndexW484).X₃ →
              (S.obj ordinaryTargetIndexW484).X₃))
  mappedExplicitCokernelEmbedding :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsEmbedding (f : X → Y)
  mappedExplicitCokernelClosedRange :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsClosed (Set.range (f : X → Y))
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
      ((normalizedLiftMapDataOfFieldsW1489 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImageOfFieldsW1489 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
          normalizedLiftLeftObjImage normalizedLiftRightObjImage Y)).app WalkingParallelPair.zero =
      (eqToHom (normalizedLiftObjImageOfFieldsW1489 normalizedLiftZeroSrc
        normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
        normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
        normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
        normalizedLiftLeftObjImage normalizedLiftRightObjImage X) ≫ τ).app WalkingParallelPair.zero
  normalizedLiftOneMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      ((normalizedLiftMapDataOfFieldsW1489 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImageOfFieldsW1489 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
          normalizedLiftLeftObjImage normalizedLiftRightObjImage Y)).app WalkingParallelPair.one =
      (eqToHom (normalizedLiftObjImageOfFieldsW1489 normalizedLiftZeroSrc
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
  endpointEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointClosedRange :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsClosed
        (Set.range ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂))
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
          localizedRightAdjointOfRawW1489
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp).obj X
  boundedHomotopyLocalizedAdjunctionUnitNaturality :
    ∀ {X Y : BoundedComplexCategory MetrizableLCA.{0}} (f : X ⟶ Y),
      f ≫ boundedHomotopyLocalizedAdjunctionUnitApp Y =
        boundedHomotopyLocalizedAdjunctionUnitApp X ≫
          (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
            localizedRightAdjointOfRawW1489
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp).map f
  boundedHomotopyLocalizedAdjunctionCounitApp :
    ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
      ((localizedRightAdjointOfRawW1489
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).obj Y ⟶
        Y
  boundedHomotopyLocalizedAdjunctionCounitNaturality :
    ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y),
      ((localizedRightAdjointOfRawW1489
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
          (localizedRightAdjointOfRawW1489
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
          (localizedRightAdjointOfRawW1489
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          boundedHomotopyLocalizedAdjunctionUnitApp
          boundedHomotopyLocalizedAdjunctionUnitNaturality
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality).app Y =
        (NatTrans.id
          ((localizedRightAdjointOfRawW1489
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp) ⋙
            𝟭 (BoundedComplexCategory MetrizableLCA.{0}))).app Y
  unitMappingConeModel :
    UnitMappingConeModelW962
  unitMappingConeEmbedding :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsEmbedding (((unitMappingConeModel X).as.sc i).f :
        ((unitMappingConeModel X).as.sc i).X₁ →
          ((unitMappingConeModel X).as.sc i).X₂)
  unitMappingConeClosedRange :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsClosed
        (Set.range (((unitMappingConeModel X).as.sc i).f :
          ((unitMappingConeModel X).as.sc i).X₁ →
            ((unitMappingConeModel X).as.sc i).X₂))
  unitMappingConeOpenMap :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsOpenMap (((unitMappingConeModel X).as.sc i).g :
        ((unitMappingConeModel X).as.sc i).X₂ →
          ((unitMappingConeModel X).as.sc i).X₃)
  unitMappingConeCokernelPreimage :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      ((unitMappingConeModel X).as.sc i).X₃ →
        ((unitMappingConeModel X).as.sc i).X₂
  unitMappingConeCokernelPreimage_eq :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₃ : ((unitMappingConeModel X).as.sc i).X₃),
        ((unitMappingConeModel X).as.sc i).g
            (unitMappingConeCokernelPreimage X i x₃) =
          x₃
  unitMappingConeKernelForward :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((unitMappingConeModel X).as.sc i).X₂),
        ((unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
            ((unitMappingConeModel X).as.sc i).f x₁ = x₂
  unitMappingConeKernelBackward :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((unitMappingConeModel X).as.sc i).X₂),
        (∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
            ((unitMappingConeModel X).as.sc i).f x₁ = x₂) →
          ((unitMappingConeModel X).as.sc i).g x₂ = 0
  unitMappingConeIsoHom :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      unitMappingConeIsoSourceW1464
          (localizedRightAdjointOfRawW1489
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfRawW1489
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
          (localizedRightAdjointOfRawW1489
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfRawW1489
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
          (localizedRightAdjointOfRawW1489
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfRawW1489
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

/-- W1489 reconstructs the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 :=
    selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1489
      input.globalClosedEmbeddingPi1Embedding
      input.globalClosedEmbeddingPi1ClosedRange
  pi2 :=
    selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1489
      input.globalClosedEmbeddingPi2Embedding
      input.globalClosedEmbeddingPi2ClosedRange
  pi3 :=
    selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1489
      input.globalClosedEmbeddingPi3Embedding
      input.globalClosedEmbeddingPi3ClosedRange

/-- W1489 builds the W519 provider from embedding and closed-range fields. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding :=
    mappedExplicitCokernelClosedEmbeddingOfFieldsW1489
      input.mappedExplicitCokernelEmbedding
      input.mappedExplicitCokernelClosedRange

/-- W1489 builds the strict-preimage object-data family from its fields. -/
def normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y :=
  fun Y =>
    normalizedLiftObjDataOfFieldsW1489 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac Y

/-- W1489 builds the strict-preimage map-data family from its fields. -/
def normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input Y)
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input Z)
        τ :=
  fun {_Y _Z} τ =>
    normalizedLiftMapDataOfFieldsW1489 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroMap
      input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
      input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
      input.normalizedLiftRightNaturality τ

/-- W1489 derives the raw lift map identity law from zero/one component laws. -/
def normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input (𝟙 Y)).natTrans =
        𝟙 (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input Y).diagram :=
  fun Y => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489,
        normalizedLiftObjDataOfFieldsW1489,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489,
        normalizedLiftMapDataOfFieldsW1489,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapId Y
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489,
        normalizedLiftObjDataOfFieldsW1489,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489,
        normalizedLiftMapDataOfFieldsW1489,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapId Y

/-- W1489 derives the raw lift map composition law from zero/one component laws. -/
def normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input (τ ≫ σ)).natTrans =
        (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input τ).natTrans ≫
          (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
            input σ).natTrans :=
  fun {_Y _Z _T} τ σ => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489,
        normalizedLiftObjDataOfFieldsW1489,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489,
        normalizedLiftMapDataOfFieldsW1489,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapComp τ σ
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489,
        normalizedLiftObjDataOfFieldsW1489,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489,
        normalizedLiftMapDataOfFieldsW1489,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapComp τ σ

/-- W1489 derives the normalized lift object-image law from four components. -/
def normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (normalizedLiftObjDataOfFieldsW1489 input.normalizedLiftZeroSrc
        input.normalizedLiftOneSrc input.normalizedLiftZeroIso
        input.normalizedLiftOneIso input.normalizedLiftLeftSrc
        input.normalizedLiftRightSrc input.normalizedLiftLeftFac
        input.normalizedLiftRightFac
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X :=
  fun X =>
    normalizedLiftObjImageOfFieldsW1489 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroObjImage
      input.normalizedLiftOneObjImage input.normalizedLiftLeftObjImage
      input.normalizedLiftRightObjImage X

/-- W1489 derives the normalized lift map-image law from zero/one components. -/
def normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
      (τ : X ⟶ Y),
      (normalizedLiftMapDataOfFieldsW1489 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
            input Y) =
      eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
            input X) ≫ τ :=
  fun {_X _Y} τ => by
    apply NatTrans.ext
    funext j
    cases j
    · exact input.normalizedLiftZeroMapImage τ
    · exact input.normalizedLiftOneMapImage τ

/-- W1489 builds the raw lift blueprint from its object and functorial fields. -/
def normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData :=
    normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input
  mapData :=
    normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input
  map_id :=
    normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input
  map_comp :=
    normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input

/-- W1489 builds the normalized lift blueprint from the raw lift fields. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input
  obj_image :=
    normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input
  map_image :=
    normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input

/-- W1489 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input

/-- W1489 reconstructs the localized right-adjoint functor fields. -/
def boundedHomotopyLocalizedRightAdjointFieldsOfW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    LocalizedRightAdjointFunctorFieldsW1467 :=
  localizedRightAdjointFunctorFieldsOfRawW1489
    input.boundedHomotopyLocalizedRightAdjointObj
    input.boundedHomotopyLocalizedRightAdjointMap
    input.boundedHomotopyLocalizedRightAdjointMapId
    input.boundedHomotopyLocalizedRightAdjointMapComp

/-- W1489 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    (boundedHomotopyLocalizedRightAdjointFieldsOfW1489 input)

/-- W1489's reconstructed right-adjoint field package keeps the object map. -/
theorem w1489LocalizedRightAdjointFieldsKeepObj
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : BoundedHomotopyLocalizedCategoryW1461) :
    (boundedHomotopyLocalizedRightAdjointFieldsOfW1489 input).obj X =
      input.boundedHomotopyLocalizedRightAdjointObj X :=
  rfl

/-- W1489's reconstructed right-adjoint field package keeps the morphism map. -/
theorem w1489LocalizedRightAdjointFieldsKeepMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y) :
    (boundedHomotopyLocalizedRightAdjointFieldsOfW1489 input).map f =
      input.boundedHomotopyLocalizedRightAdjointMap f :=
  rfl

/-- W1489's reconstructed right adjoint keeps the object map. -/
theorem w1489LocalizedRightAdjointKeepsObj
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : BoundedHomotopyLocalizedCategoryW1461) :
    (boundedHomotopyLocalizedRightAdjointOfW1489 input).obj X =
      input.boundedHomotopyLocalizedRightAdjointObj X :=
  rfl

/-- W1489's reconstructed right adjoint keeps the morphism map. -/
theorem w1489LocalizedRightAdjointKeepsMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y) :
    (boundedHomotopyLocalizedRightAdjointOfW1489 input).map f =
      input.boundedHomotopyLocalizedRightAdjointMap f :=
  rfl

/-- W1489 reconstructs the target-difference surjectivity provider. -/
def targetDifferenceSurjectiveForTargetProviderOfW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y :=
  targetDifferenceSurjectivePrimitiveOfWitnessW1489
    input.targetDifferenceSurjectivePreimage
    input.targetDifferenceSurjectivePreimageSpec

/-- W1489 reconstructs the target-codomain compact no-univ membership provider. -/
def targetCodomainCompactNoUnivMembershipProviderOfW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y :=
  targetCodomainCompactNoUnivMembershipPrimitiveOfWitnessW1489
    input.targetCodomainCompactMeetPoint
    input.targetCodomainCompactMeetSpec

/-- W1489's target-difference witness field satisfies the selected preimage equation. -/
theorem w1489TargetDifferenceSurjectiveWitnessSpec
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    (y : wppOpCodomainW441 Y) :
    (((wppOpLeftW441 Y - wppOpRightW441 Y) :
      wppOpDomainW441 Y ⟶ wppOpCodomainW441 Y) :
      wppOpDomainW441 Y → wppOpCodomainW441 Y)
      (input.targetDifferenceSurjectivePreimage Y y) = y :=
  input.targetDifferenceSurjectivePreimageSpec Y y

/-- W1489's compactness witness field satisfies the selected neighbourhood-meet equation. -/
theorem w1489TargetCodomainCompactWitnessSpec
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    {f : Filter (wppOpCodomainW441 Y)} (hf : f ≠ ⊥) :
    (𝓝 (input.targetCodomainCompactMeetPoint Y (f := f) hf) ⊓ f) ≠ ⊥ :=
  input.targetCodomainCompactMeetSpec Y (f := f) hf

/-- W1489 builds the W1477 input after reconstructing the map-data family. -/
def w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    targetDifferenceSurjectiveForTargetProviderOfW1489 input
  targetCodomainCompactNoUnivMembershipProvider :=
    targetCodomainCompactNoUnivMembershipProviderOfW1489 input
  globalClosedEmbeddingPi1 :=
    selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1489
      input.globalClosedEmbeddingPi1Embedding
      input.globalClosedEmbeddingPi1ClosedRange
  globalClosedEmbeddingPi2 :=
    selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1489
      input.globalClosedEmbeddingPi2Embedding
      input.globalClosedEmbeddingPi2ClosedRange
  globalClosedEmbeddingPi3 :=
    selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1489
      input.globalClosedEmbeddingPi3Embedding
      input.globalClosedEmbeddingPi3ClosedRange
  mappedExplicitCokernelClosedEmbedding :=
    mappedExplicitCokernelClosedEmbeddingOfFieldsW1489
      input.mappedExplicitCokernelEmbedding
      input.mappedExplicitCokernelClosedRange
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
    normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input
  normalizedLiftZeroMapImage := input.normalizedLiftZeroMapImage
  normalizedLiftOneMapImage := input.normalizedLiftOneMapImage
  targetFixedTargetUniq := input.targetFixedTargetUniq
  localizationModelFixedTargetUniq := input.localizationModelFixedTargetUniq
  sourcePretriangulated := input.sourcePretriangulated
  sourceTriangulated := input.sourceTriangulated
  triangleCompletion := input.triangleCompletion
  endpointClosedEmbedding :=
    endpointClosedEmbeddingOfFieldsW1489
      input.endpointEmbedding
      input.endpointClosedRange
  endpointOpenMap := input.endpointOpenMap
  endpointCokernelTop := input.endpointCokernelTop
  endpointKernelEquality := input.endpointKernelEquality
  boundedHomotopyLocalizedRightAdjointFields :=
    boundedHomotopyLocalizedRightAdjointFieldsOfW1489 input
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
  unitMappingConeClosedEmbedding :=
    unitMappingConeClosedEmbeddingOfFieldsW1489
      input.unitMappingConeModel
      input.unitMappingConeEmbedding
      input.unitMappingConeClosedRange
  unitMappingConeOpenMap := input.unitMappingConeOpenMap
  unitMappingConeCokernelTop :=
    unitMappingConeCokernelTopOfWitnessW1489
      input.unitMappingConeModel
      input.unitMappingConeCokernelPreimage
      input.unitMappingConeCokernelPreimage_eq
  unitMappingConeKernelEquality :=
    unitMappingConeKernelEqualityOfFieldsW1489
      input.unitMappingConeModel
      input.unitMappingConeKernelForward
      input.unitMappingConeKernelBackward
  unitMappingConeIsoHom := input.unitMappingConeIsoHom
  unitMappingConeIsoInv := input.unitMappingConeIsoInv
  unitMappingConeIsoHomInvId := input.unitMappingConeIsoHomInvId
  unitMappingConeIsoInvHomId := input.unitMappingConeIsoInvHomId

/-- W1489 builds W945 localized-unit data through W1477. -/
def localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input)

/-- W1489 builds W730 boundary/relation data through W1477. -/
def boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input)

/-- W1489 builds W986 target/endpoint data through W1477. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input)

/-- W1489 builds W987 full data through W1477. -/
noncomputable def fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
      input)

/-- W1489's first selected-difference closed embedding keeps the embedding field. -/
theorem w1489SelectedDifferenceClosedEmbeddingPi1KeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi1Embedding
        input.globalClosedEmbeddingPi1ClosedRange S).toIsEmbedding =
      input.globalClosedEmbeddingPi1Embedding S :=
  rfl

/-- W1489's first selected-difference closed embedding keeps the closed-range field. -/
theorem w1489SelectedDifferenceClosedEmbeddingPi1KeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi1Embedding
        input.globalClosedEmbeddingPi1ClosedRange S).isClosed_range =
      input.globalClosedEmbeddingPi1ClosedRange S :=
  rfl

/-- W1489's constructed W718 provider keeps the reconstructed first component field. -/
theorem w1489GlobalClosedEmbeddingComponentsKeepsConstructedPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi1Embedding
        input.globalClosedEmbeddingPi1ClosedRange :=
  rfl

/-- W1489's second selected-difference closed embedding keeps the embedding field. -/
theorem w1489SelectedDifferenceClosedEmbeddingPi2KeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi2Embedding
        input.globalClosedEmbeddingPi2ClosedRange S).toIsEmbedding =
      input.globalClosedEmbeddingPi2Embedding S :=
  rfl

/-- W1489's second selected-difference closed embedding keeps the closed-range field. -/
theorem w1489SelectedDifferenceClosedEmbeddingPi2KeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi2Embedding
        input.globalClosedEmbeddingPi2ClosedRange S).isClosed_range =
      input.globalClosedEmbeddingPi2ClosedRange S :=
  rfl

/-- W1489's constructed W718 provider keeps the reconstructed second component field. -/
theorem w1489GlobalClosedEmbeddingComponentsKeepsConstructedPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi2Embedding
        input.globalClosedEmbeddingPi2ClosedRange :=
  rfl

/-- W1489's third selected-difference closed embedding keeps the embedding field. -/
theorem w1489SelectedDifferenceClosedEmbeddingPi3KeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi3Embedding
        input.globalClosedEmbeddingPi3ClosedRange S).toIsEmbedding =
      input.globalClosedEmbeddingPi3Embedding S :=
  rfl

/-- W1489's third selected-difference closed embedding keeps the closed-range field. -/
theorem w1489SelectedDifferenceClosedEmbeddingPi3KeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi3Embedding
        input.globalClosedEmbeddingPi3ClosedRange S).isClosed_range =
      input.globalClosedEmbeddingPi3ClosedRange S :=
  rfl

/-- W1489's constructed W718 provider keeps the reconstructed third component field. -/
theorem w1489GlobalClosedEmbeddingComponentsKeepsConstructedPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi3Embedding
        input.globalClosedEmbeddingPi3ClosedRange :=
  rfl

/-- W1489's constructed W973 data keeps the constructed W718 provider. -/
theorem w1489ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input :=
  rfl

/-- W1489's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1489ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input :=
  rfl

/-- W1489's reconstructed closed embedding keeps the embedding field. -/
theorem w1489MappedExplicitCokernelClosedEmbeddingKeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedExplicitCokernelClosedEmbeddingOfFieldsW1489
        input.mappedExplicitCokernelEmbedding
        input.mappedExplicitCokernelClosedRange f).toIsEmbedding =
      input.mappedExplicitCokernelEmbedding f :=
  rfl

/-- W1489's reconstructed closed embedding keeps the closed-range field. -/
theorem w1489MappedExplicitCokernelClosedEmbeddingKeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedExplicitCokernelClosedEmbeddingOfFieldsW1489
        input.mappedExplicitCokernelEmbedding
        input.mappedExplicitCokernelClosedRange f).isClosed_range =
      input.mappedExplicitCokernelClosedRange f :=
  rfl

/-- W1489's constructed W519 provider keeps the reconstructed closed embedding. -/
theorem w1489MappedCokernelClosedEmbeddingProviderKeepsConstructedField
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).isClosedEmbedding f =
      mappedExplicitCokernelClosedEmbeddingOfFieldsW1489
        input.mappedExplicitCokernelEmbedding
        input.mappedExplicitCokernelClosedRange f :=
  rfl

/-- W1489's endpoint closed embedding keeps the embedding field. -/
theorem w1489EndpointClosedEmbeddingKeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    (endpointClosedEmbeddingOfFieldsW1489
        input.endpointEmbedding input.endpointClosedRange K i).toIsEmbedding =
      input.endpointEmbedding K i :=
  rfl

/-- W1489's endpoint closed embedding keeps the closed-range field. -/
theorem w1489EndpointClosedEmbeddingKeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    (endpointClosedEmbeddingOfFieldsW1489
        input.endpointEmbedding input.endpointClosedRange K i).isClosed_range =
      input.endpointClosedRange K i :=
  rfl

/-- W1489's unit mapping-cone closed embedding keeps the embedding field. -/
theorem w1489UnitMappingConeClosedEmbeddingKeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    (unitMappingConeClosedEmbeddingOfFieldsW1489
        input.unitMappingConeModel input.unitMappingConeEmbedding
        input.unitMappingConeClosedRange X i).toIsEmbedding =
      input.unitMappingConeEmbedding X i :=
  rfl

/-- W1489's unit mapping-cone closed embedding keeps the closed-range field. -/
theorem w1489UnitMappingConeClosedEmbeddingKeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    (unitMappingConeClosedEmbeddingOfFieldsW1489
        input.unitMappingConeModel input.unitMappingConeEmbedding
        input.unitMappingConeClosedRange X i).isClosed_range =
      input.unitMappingConeClosedRange X i :=
  rfl

/-- W1489's unit mapping-cone cokernel-top witness gives surjectivity. -/
theorem w1489UnitMappingConeCokernelTopWitnessSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    Function.Surjective (((input.unitMappingConeModel X).as.sc i).g :
      ((input.unitMappingConeModel X).as.sc i).X₂ →
        ((input.unitMappingConeModel X).as.sc i).X₃) := by
  intro x₃
  exact ⟨input.unitMappingConeCokernelPreimage X i x₃,
    input.unitMappingConeCokernelPreimage_eq X i x₃⟩

/-- W1489's unit mapping-cone cokernel-top witness keeps its equation field. -/
theorem w1489UnitMappingConeCokernelTopWitnessSpec
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
    (x₃ : ((input.unitMappingConeModel X).as.sc i).X₃) :
    ((input.unitMappingConeModel X).as.sc i).g
        (input.unitMappingConeCokernelPreimage X i x₃) =
      x₃ :=
  input.unitMappingConeCokernelPreimage_eq X i x₃

/-- W1489's unit mapping-cone kernel equality keeps the forward implication. -/
theorem w1489UnitMappingConeKernelEqualityKeepsForward
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
    (x₂ : ((input.unitMappingConeModel X).as.sc i).X₂)
    (h : ((input.unitMappingConeModel X).as.sc i).g x₂ = 0) :
    (unitMappingConeKernelEqualityOfFieldsW1489
        input.unitMappingConeModel
        input.unitMappingConeKernelForward
        input.unitMappingConeKernelBackward X i x₂).mp h =
      input.unitMappingConeKernelForward X i x₂ h :=
  rfl

/-- W1489's unit mapping-cone kernel equality keeps the backward implication. -/
theorem w1489UnitMappingConeKernelEqualityKeepsBackward
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
    (x₂ : ((input.unitMappingConeModel X).as.sc i).X₂)
    (h :
      ∃ x₁ : ((input.unitMappingConeModel X).as.sc i).X₁,
        ((input.unitMappingConeModel X).as.sc i).f x₁ = x₂) :
    (unitMappingConeKernelEqualityOfFieldsW1489
        input.unitMappingConeModel
        input.unitMappingConeKernelForward
        input.unitMappingConeKernelBackward X i x₂).mpr h =
      input.unitMappingConeKernelBackward X i x₂ h :=
  rfl

/-- W1489's object-data family keeps the zero object field. -/
theorem w1489NormalizedLiftObjDataKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input Y).zeroSrc =
      input.normalizedLiftZeroSrc Y :=
  rfl

/-- W1489's object-data family keeps the one object field. -/
theorem w1489NormalizedLiftObjDataKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input Y).oneSrc =
      input.normalizedLiftOneSrc Y :=
  rfl

/-- W1489's object-data family keeps the zero comparison isomorphism. -/
theorem w1489NormalizedLiftObjDataKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input Y).zeroIso =
      input.normalizedLiftZeroIso Y :=
  rfl

/-- W1489's object-data family keeps the one comparison isomorphism. -/
theorem w1489NormalizedLiftObjDataKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input Y).oneIso =
      input.normalizedLiftOneIso Y :=
  rfl

/-- W1489's object-data family keeps the left source map. -/
theorem w1489NormalizedLiftObjDataKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input Y).leftSrc =
      input.normalizedLiftLeftSrc Y :=
  rfl

/-- W1489's object-data family keeps the right source map. -/
theorem w1489NormalizedLiftObjDataKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input Y).rightSrc =
      input.normalizedLiftRightSrc Y :=
  rfl

/-- W1489's object-data family keeps the left factorization law. -/
theorem w1489NormalizedLiftObjDataKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input Y).left_fac =
      input.normalizedLiftLeftFac Y :=
  rfl

/-- W1489's object-data family keeps the right factorization law. -/
theorem w1489NormalizedLiftObjDataKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input Y).right_fac =
      input.normalizedLiftRightFac Y :=
  rfl

/-- W1489's map-data family keeps the zero map field. -/
theorem w1489NormalizedLiftMapDataKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input τ).zeroMap =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1489's map-data family keeps the one map field. -/
theorem w1489NormalizedLiftMapDataKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input τ).oneMap =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1489's map-data family keeps the zero-map factorization law. -/
theorem w1489NormalizedLiftMapDataKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input τ).zero_fac =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1489's map-data family keeps the one-map factorization law. -/
theorem w1489NormalizedLiftMapDataKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input τ).one_fac =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1489's map-data family keeps the left naturality law. -/
theorem w1489NormalizedLiftMapDataKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input τ).left_naturality =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1489's map-data family keeps the right naturality law. -/
theorem w1489NormalizedLiftMapDataKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input τ).right_naturality =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1489's raw lift blueprint keeps the constructed object-data family. -/
theorem w1489NormalizedLiftRawBlueprintKeepsConstructedObjData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).objData =
      normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input :=
  rfl

/-- W1489's raw lift blueprint keeps the constructed map-data family. -/
theorem w1489NormalizedLiftRawBlueprintKeepsConstructedMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).mapData τ =
      normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input τ :=
  rfl

/-- W1489's raw lift blueprint keeps the constructed identity law. -/
theorem w1489NormalizedLiftRawBlueprintKeepsMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).map_id Y =
      normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input Y :=
  rfl

/-- W1489's raw lift blueprint keeps the constructed composition law. -/
theorem w1489NormalizedLiftRawBlueprintKeepsMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).map_comp τ σ =
      normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input τ σ :=
  rfl

/-- W1489's normalized lift blueprint keeps the constructed raw lift blueprint. -/
theorem w1489NormalizedLiftBlueprintKeepsConstructedRawBlueprint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).blueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input :=
  rfl

/-- W1489's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1489NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).obj_image X =
      normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input X :=
  rfl

/-- W1489's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1489NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).map_image τ =
      normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input τ :=
  rfl

/-- W1489's input keeps the zero component map-image normalization law. -/
theorem w1489NormalizedLiftMapImageKeepsZeroComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1489 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
            input Y)).app WalkingParallelPair.zero =
      (eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
            input X) ≫ τ).app WalkingParallelPair.zero := by
  simpa [normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489]
    using input.normalizedLiftZeroMapImage τ

/-- W1489's input keeps the one component map-image normalization law. -/
theorem w1489NormalizedLiftMapImageKeepsOneComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1489 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
            input Y)).app WalkingParallelPair.one =
      (eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
            input X) ≫ τ).app WalkingParallelPair.one := by
  simpa [normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489]
    using input.normalizedLiftOneMapImage τ

/-- W1489's W1477 input keeps the reconstructed first W718 component field. -/
theorem w1489W1477InputKeepsConstructedGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).globalClosedEmbeddingPi1 =
      selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi1Embedding
        input.globalClosedEmbeddingPi1ClosedRange :=
  rfl

/-- W1489's W1477 input keeps the reconstructed second W718 component field. -/
theorem w1489W1477InputKeepsConstructedGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).globalClosedEmbeddingPi2 =
      selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi2Embedding
        input.globalClosedEmbeddingPi2ClosedRange :=
  rfl

/-- W1489's W1477 input keeps the reconstructed third W718 component field. -/
theorem w1489W1477InputKeepsConstructedGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).globalClosedEmbeddingPi3 =
      selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1489
        input.globalClosedEmbeddingPi3Embedding
        input.globalClosedEmbeddingPi3ClosedRange :=
  rfl

/-- W1489's W1477 input keeps W519 mapped-cokernel data. -/
theorem w1489W1477InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input :=
  rfl

/-- W1489's W1477 input keeps the reconstructed endpoint closed-embedding family. -/
theorem w1489W1477InputKeepsConstructedEndpointClosedEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).endpointClosedEmbedding =
      endpointClosedEmbeddingOfFieldsW1489
        input.endpointEmbedding
        input.endpointClosedRange :=
  rfl

/-- W1489's W1477 input keeps the reconstructed unit mapping-cone closed-embedding family. -/
theorem w1489W1477InputKeepsConstructedUnitMappingConeClosedEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).unitMappingConeClosedEmbedding =
      unitMappingConeClosedEmbeddingOfFieldsW1489
        input.unitMappingConeModel
        input.unitMappingConeEmbedding
      input.unitMappingConeClosedRange :=
  rfl

/-- W1489's W1477 input keeps the reconstructed unit mapping-cone cokernel-top family. -/
theorem w1489W1477InputKeepsConstructedUnitMappingConeCokernelTop
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).unitMappingConeCokernelTop =
      unitMappingConeCokernelTopOfWitnessW1489
        input.unitMappingConeModel
        input.unitMappingConeCokernelPreimage
        input.unitMappingConeCokernelPreimage_eq :=
  rfl

/-- W1489's W1477 input keeps the reconstructed unit mapping-cone kernel equality. -/
theorem w1489W1477InputKeepsConstructedUnitMappingConeKernelEquality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).unitMappingConeKernelEquality =
      unitMappingConeKernelEqualityOfFieldsW1489
        input.unitMappingConeModel
        input.unitMappingConeKernelForward
        input.unitMappingConeKernelBackward :=
  rfl

/-- W1489's W1477 input keeps the zero source object field. -/
theorem w1489W1477InputKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftZeroSrc =
      input.normalizedLiftZeroSrc :=
  rfl

/-- W1489's W1477 input keeps the one source object field. -/
theorem w1489W1477InputKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftOneSrc =
      input.normalizedLiftOneSrc :=
  rfl

/-- W1489's W1477 input keeps the zero comparison isomorphism. -/
theorem w1489W1477InputKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftZeroIso =
      input.normalizedLiftZeroIso :=
  rfl

/-- W1489's W1477 input keeps the one comparison isomorphism. -/
theorem w1489W1477InputKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftOneIso =
      input.normalizedLiftOneIso :=
  rfl

/-- W1489's W1477 input keeps the left source map. -/
theorem w1489W1477InputKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftLeftSrc =
      input.normalizedLiftLeftSrc :=
  rfl

/-- W1489's W1477 input keeps the right source map. -/
theorem w1489W1477InputKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftRightSrc =
      input.normalizedLiftRightSrc :=
  rfl

/-- W1489's W1477 input keeps the left factorization law. -/
theorem w1489W1477InputKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftLeftFac =
      input.normalizedLiftLeftFac :=
  rfl

/-- W1489's W1477 input keeps the right factorization law. -/
theorem w1489W1477InputKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftRightFac =
      input.normalizedLiftRightFac :=
  rfl

/-- W1489's W1477 input keeps the zero map field. -/
theorem w1489W1477InputKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftZeroMap τ =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1489's W1477 input keeps the one map field. -/
theorem w1489W1477InputKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftOneMap τ =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1489's W1477 input keeps the zero-map factorization law. -/
theorem w1489W1477InputKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftZeroMapFac τ =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1489's W1477 input keeps the one-map factorization law. -/
theorem w1489W1477InputKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftOneMapFac τ =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1489's W1477 input keeps the left naturality law. -/
theorem w1489W1477InputKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftLeftNaturality τ =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1489's W1477 input keeps the right naturality law. -/
theorem w1489W1477InputKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftRightNaturality τ =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1489's W1477 input keeps the zero-map identity law. -/
theorem w1489W1477InputKeepsZeroMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftZeroMapId Y =
      input.normalizedLiftZeroMapId Y :=
  rfl

/-- W1489's W1477 input keeps the one-map identity law. -/
theorem w1489W1477InputKeepsOneMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftOneMapId Y =
      input.normalizedLiftOneMapId Y :=
  rfl

/-- W1489's W1477 input keeps the zero-map composition law. -/
theorem w1489W1477InputKeepsZeroMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftZeroMapComp τ σ =
      input.normalizedLiftZeroMapComp τ σ :=
  rfl

/-- W1489's W1477 input keeps the one-map composition law. -/
theorem w1489W1477InputKeepsOneMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftOneMapComp τ σ =
      input.normalizedLiftOneMapComp τ σ :=
  rfl

/-- W1489's W1477 input keeps the object-image normalization field. -/
theorem w1489W1477InputKeepsNormalizedLiftObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftObjImage X =
      normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input X :=
  rfl

/-- W1489's W1477 input keeps the zero-component map-image normalization field. -/
theorem w1489W1477InputKeepsNormalizedLiftZeroMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftZeroMapImage τ =
      input.normalizedLiftZeroMapImage τ :=
  rfl

/-- W1489's W1477 input keeps the one-component map-image normalization field. -/
theorem w1489W1477InputKeepsNormalizedLiftOneMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).normalizedLiftOneMapImage τ =
      input.normalizedLiftOneMapImage τ :=
  rfl

/-- W1489's W1477 input keeps target-difference surjectivity. -/
theorem w1489W1477InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).targetDifferenceSurjectiveForTargetProvider =
      targetDifferenceSurjectiveForTargetProviderOfW1489 input :=
  rfl

/-- W1489's W1477 input keeps target-codomain compact no-univ membership. -/
theorem w1489W1477InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input).targetCodomainCompactNoUnivMembershipProvider =
      targetCodomainCompactNoUnivMembershipProviderOfW1489 input :=
  rfl

/-- W1489's W1477 input keeps the reconstructed localized right adjoint. -/
theorem w1489W1477InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    boundedHomotopyLocalizedRightAdjointOfW1477
        (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1489 input :=
  rfl

/-- W1489's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1489LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1489 input :=
  rfl

/-- W1489's W986 construction keeps the constructed W973 closedness data. -/
theorem w1489TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input :=
  rfl

/-- W1489's constructed W987 provider projects to the constructed W730 data. -/
theorem w1489FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input :=
  rfl

/-- W1489's constructed W987 provider projects to the constructed W986 data. -/
theorem w1489FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489
        input :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1489 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
      "raw closed-natural-transformation target-relation-lifts provider",
      "target-difference surjectivity preimage chooser family",
      "target-difference surjectivity preimage equation family",
      "target-codomain compact no-univ membership point chooser family",
      "target-codomain compact no-univ membership neighbourhood-meet equation family",
      "first selected-difference closed-embedding diagram embedding field",
      "first selected-difference closed-embedding diagram closed-range field",
      "second selected-difference closed-embedding diagram embedding field",
      "second selected-difference closed-embedding diagram closed-range field",
      "third selected-difference closed-embedding diagram embedding field",
      "third selected-difference closed-embedding diagram closed-range field",
    "mapped explicit cokernel embedding raw field",
    "mapped explicit cokernel closed-range raw field",
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
    "endpoint incoming-map embedding family",
    "endpoint incoming-map closed-range family",
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
    "unit mapping-cone incoming-map embedding family",
    "unit mapping-cone incoming-map closed-range family",
    "unit mapping-cone open-map family",
    "unit mapping-cone cokernel preimage chooser family",
    "unit mapping-cone cokernel preimage equation family",
    "unit mapping-cone kernel forward implication family",
    "unit mapping-cone kernel backward implication family",
    "unit mapping-cone isomorphism hom",
    "unit mapping-cone isomorphism inv",
    "unit mapping-cone isomorphism hom-inv identity",
    "unit mapping-cone isomorphism inv-hom identity"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1489_count :
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1489.length =
        72 :=
    rfl

/-- W1489 records the bundled first selected-difference closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1489 :
    List String :=
  ["first selected-difference closed-embedding diagram component field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1489.length =
      1 :=
  rfl

/-- W1489 records the component first selected-difference closed-embedding inputs. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1489 :
    List String :=
  ["first selected-difference closed-embedding diagram embedding field",
    "first selected-difference closed-embedding diagram closed-range field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one first selected-difference closed-embedding field by component fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi1Input :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1489_count]
  decide

/-- W1489 records the bundled second selected-difference closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1489 :
    List String :=
  ["second selected-difference closed-embedding diagram component field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1489.length =
      1 :=
  rfl

/-- W1489 records the component second selected-difference closed-embedding inputs. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1489 :
    List String :=
  ["second selected-difference closed-embedding diagram embedding field",
    "second selected-difference closed-embedding diagram closed-range field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one second selected-difference closed-embedding field by component fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi2Input :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1489_count]
  decide

/-- W1489 records the bundled third selected-difference closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1489 :
    List String :=
  ["third selected-difference closed-embedding diagram component field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1489.length =
      1 :=
  rfl

/-- W1489 records the component third selected-difference closed-embedding inputs. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1489 :
    List String :=
  ["third selected-difference closed-embedding diagram embedding field",
    "third selected-difference closed-embedding diagram closed-range field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one third selected-difference closed-embedding field by component fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi3Input :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1489_count]
  decide

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1489 :
    List String :=
  ["normalized lift object-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1489.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1489 :
    List String :=
  ["normalized lift zero object-image normalization",
    "normalized lift one object-image normalization",
    "normalized lift left arrow-image normalization",
    "normalized lift right arrow-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1489.length =
      4 :=
  rfl

/-- W1489 replaces one object-image law by four component image laws. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsObjectImageInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1489_count]
  decide

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1489 :
    List String :=
  ["bounded homotopy localized right-adjoint functor field package"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1489.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1489 :
    List String :=
  ["bounded homotopy localized right-adjoint object map",
    "bounded homotopy localized right-adjoint morphism map",
    "bounded homotopy localized right-adjoint identity law",
    "bounded homotopy localized right-adjoint composition law"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1489.length =
      4 :=
  rfl

/-- W1489 replaces one right-adjoint functor package by four functor fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsRightAdjointInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1489_count]
  decide

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1489 :
    List String :=
  ["target-difference surjectivity primitive family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1489.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1489 :
    List String :=
  ["target-difference surjectivity preimage chooser family",
    "target-difference surjectivity preimage equation family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one target-surjectivity primitive family by witness fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsTargetSurjectivityInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1489_count]
  decide

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1489 :
    List String :=
  ["target-codomain compact no-univ membership primitive family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1489.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1489 :
    List String :=
  ["target-codomain compact no-univ membership point chooser family",
    "target-codomain compact no-univ membership neighbourhood-meet equation family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one target compactness primitive family by witness fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsTargetCompactnessInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1489_count]
  decide

/-- W1489 records the bundled mapped explicit cokernel closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1489 :
    List String :=
  ["mapped explicit cokernel closed-embedding raw field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1489.length =
      1 :=
  rfl

/-- W1489 records the component mapped explicit cokernel input fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1489 :
    List String :=
  ["mapped explicit cokernel embedding raw field",
    "mapped explicit cokernel closed-range raw field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one mapped explicit cokernel closed-embedding field by two component fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsMappedCokernelInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1489_count]
  decide

/-- W1489 records the bundled endpoint closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1489 :
    List String :=
  ["endpoint closed-embedding family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1489.length =
      1 :=
  rfl

/-- W1489 records the component endpoint closed-embedding input fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1489 :
    List String :=
  ["endpoint incoming-map embedding family",
    "endpoint incoming-map closed-range family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one endpoint closed-embedding family by two component fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsEndpointClosedEmbeddingInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1489_count]
  decide

/-- W1489 records the bundled unit mapping-cone closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1489 :
    List String :=
  ["unit mapping-cone closed-embedding family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1489.length =
      1 :=
  rfl

/-- W1489 records the component unit mapping-cone closed-embedding input fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1489 :
    List String :=
  ["unit mapping-cone incoming-map embedding family",
    "unit mapping-cone incoming-map closed-range family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one unit mapping-cone closed-embedding family by two component fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeClosedEmbeddingInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1489_count]
  decide

/-- W1489 records the bundled unit mapping-cone cokernel-top input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1489 :
    List String :=
  ["unit mapping-cone cokernel-top family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1489.length =
      1 :=
  rfl

/-- W1489 records the component unit mapping-cone cokernel-top witness fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1489 :
    List String :=
  ["unit mapping-cone cokernel preimage chooser family",
    "unit mapping-cone cokernel preimage equation family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one unit mapping-cone cokernel-top family by two witness fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeCokernelTopInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1489_count]
  decide

/-- W1489 records the bundled unit mapping-cone kernel-equality input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1489 :
    List String :=
  ["unit mapping-cone kernel-equality family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1489.length =
      1 :=
  rfl

/-- W1489 records the component unit mapping-cone kernel-equality input fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1489 :
    List String :=
  ["unit mapping-cone kernel forward implication family",
    "unit mapping-cone kernel backward implication family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1489_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1489.length =
      2 :=
  rfl

/-- W1489 replaces one unit mapping-cone kernel-equality family by two implication fields. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeKernelEqualityInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1489.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1489_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1489_count]
  decide

/-- W1489 expands the W1488 input ledger after splitting the unit mapping-cone cokernel top. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionExpandsW1488InputCount :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1488.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1488_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1489_count]
  decide

/-- W1489 expands the W1477 input count after splitting the unit mapping-cone kernel equality. -/
theorem w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionExpandsW1477InputCount :
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1489.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1489_count]
  decide

/-- Current W1489 nonterminal strict-preimage object-image right-adjoint functor target-compactness construction state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionStateW1489 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  objectImageInputNames : List String
  componentObjectImageInputNames : List String
  targetSurjectivityInputNames : List String
  componentTargetSurjectivityInputNames : List String
  targetCompactnessInputNames : List String
  componentTargetCompactnessInputNames : List String
  mappedCokernelInputNames : List String
  componentMappedCokernelInputNames : List String
  endpointClosedEmbeddingInputNames : List String
  componentEndpointClosedEmbeddingInputNames : List String
  unitMappingConeClosedEmbeddingInputNames : List String
  componentUnitMappingConeClosedEmbeddingInputNames : List String
  unitMappingConeCokernelTopInputNames : List String
  componentUnitMappingConeCokernelTopInputNames : List String
  unitMappingConeKernelEqualityInputNames : List String
  componentUnitMappingConeKernelEqualityInputNames : List String
  selectedDifferencePi1InputNames : List String
  componentSelectedDifferencePi1InputNames : List String
  selectedDifferencePi2InputNames : List String
  componentSelectedDifferencePi2InputNames : List String
  selectedDifferencePi3InputNames : List String
  componentSelectedDifferencePi3InputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1489 records the strict-preimage object-image right-adjoint functor target-compactness construction path. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionStateW1489 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionStateW1489 where
  seed :=
    "w1489-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-endpoint-unit-mapping-cone-cokernel-top-witness-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1489",
      "normalizedLiftObjDataOfFieldsW1489",
      "normalizedLiftMapDataOfFieldsW1489",
      "normalizedLiftObjImageOfFieldsW1489",
      "localizedRightAdjointFunctorFieldsOfRawW1489",
      "localizedRightAdjointOfRawW1489",
      "targetDifferenceSurjectivePrimitiveOfWitnessW1489",
      "targetCodomainCompactNoUnivMembershipPrimitiveOfWitnessW1489",
      "mappedExplicitCokernelClosedEmbeddingOfFieldsW1489",
      "endpointClosedEmbeddingOfFieldsW1489",
      "unitMappingConeClosedEmbeddingOfFieldsW1489",
      "unitMappingConeCokernelTopOfWitnessW1489",
      "unitMappingConeKernelEqualityOfFieldsW1489",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "boundedHomotopyLocalizedRightAdjointFieldsOfW1489",
      "boundedHomotopyLocalizedRightAdjointOfW1489",
      "w1489LocalizedRightAdjointFieldsKeepObj",
      "w1489LocalizedRightAdjointFieldsKeepMap",
      "w1489LocalizedRightAdjointKeepsObj",
      "w1489LocalizedRightAdjointKeepsMap",
      "targetDifferenceSurjectiveForTargetProviderOfW1489",
      "targetCodomainCompactNoUnivMembershipProviderOfW1489",
      "w1489TargetDifferenceSurjectiveWitnessSpec",
      "w1489TargetCodomainCompactWitnessSpec",
      "w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
            "fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1489",
            "selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1489",
            "selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1489",
            "selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1489",
            "w1489SelectedDifferenceClosedEmbeddingPi1KeepsEmbedding",
            "w1489SelectedDifferenceClosedEmbeddingPi1KeepsClosedRange",
            "w1489SelectedDifferenceClosedEmbeddingPi2KeepsEmbedding",
            "w1489SelectedDifferenceClosedEmbeddingPi2KeepsClosedRange",
            "w1489SelectedDifferenceClosedEmbeddingPi3KeepsEmbedding",
            "w1489SelectedDifferenceClosedEmbeddingPi3KeepsClosedRange",
            "w1489GlobalClosedEmbeddingComponentsKeepsConstructedPi1",
            "w1489GlobalClosedEmbeddingComponentsKeepsConstructedPi2",
            "w1489GlobalClosedEmbeddingComponentsKeepsConstructedPi3",
      "w1489ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1489ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1489MappedExplicitCokernelClosedEmbeddingKeepsEmbedding",
      "w1489MappedExplicitCokernelClosedEmbeddingKeepsClosedRange",
      "w1489MappedCokernelClosedEmbeddingProviderKeepsConstructedField",
      "w1489EndpointClosedEmbeddingKeepsEmbedding",
      "w1489EndpointClosedEmbeddingKeepsClosedRange",
      "w1489UnitMappingConeClosedEmbeddingKeepsEmbedding",
      "w1489UnitMappingConeClosedEmbeddingKeepsClosedRange",
      "w1489UnitMappingConeCokernelTopWitnessSurjective",
      "w1489UnitMappingConeCokernelTopWitnessSpec",
      "w1489UnitMappingConeKernelEqualityKeepsForward",
      "w1489UnitMappingConeKernelEqualityKeepsBackward",
      "w1489NormalizedLiftObjDataKeepsZeroSrc",
      "w1489NormalizedLiftObjDataKeepsOneSrc",
      "w1489NormalizedLiftObjDataKeepsZeroIso",
      "w1489NormalizedLiftObjDataKeepsOneIso",
      "w1489NormalizedLiftObjDataKeepsLeftSrc",
      "w1489NormalizedLiftObjDataKeepsRightSrc",
      "w1489NormalizedLiftObjDataKeepsLeftFac",
      "w1489NormalizedLiftObjDataKeepsRightFac",
      "w1489NormalizedLiftMapDataKeepsZeroMap",
      "w1489NormalizedLiftMapDataKeepsOneMap",
      "w1489NormalizedLiftMapDataKeepsZeroMapFac",
      "w1489NormalizedLiftMapDataKeepsOneMapFac",
      "w1489NormalizedLiftMapDataKeepsLeftNaturality",
      "w1489NormalizedLiftMapDataKeepsRightNaturality",
      "w1489NormalizedLiftRawBlueprintKeepsConstructedObjData",
      "w1489NormalizedLiftRawBlueprintKeepsConstructedMapData",
      "w1489NormalizedLiftRawBlueprintKeepsMapId",
      "w1489NormalizedLiftRawBlueprintKeepsMapComp",
      "w1489NormalizedLiftBlueprintKeepsConstructedRawBlueprint",
      "w1489NormalizedLiftBlueprintKeepsObjImage",
      "w1489NormalizedLiftBlueprintKeepsMapImage",
            "w1489NormalizedLiftMapImageKeepsZeroComponent",
            "w1489NormalizedLiftMapImageKeepsOneComponent",
            "w1489W1477InputKeepsConstructedGlobalClosedEmbeddingPi1",
            "w1489W1477InputKeepsConstructedGlobalClosedEmbeddingPi2",
            "w1489W1477InputKeepsConstructedGlobalClosedEmbeddingPi3",
      "w1489W1477InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1489W1477InputKeepsConstructedEndpointClosedEmbedding",
      "w1489W1477InputKeepsConstructedUnitMappingConeClosedEmbedding",
      "w1489W1477InputKeepsConstructedUnitMappingConeCokernelTop",
      "w1489W1477InputKeepsConstructedUnitMappingConeKernelEquality",
      "w1489W1477InputKeepsZeroSrc",
      "w1489W1477InputKeepsOneSrc",
      "w1489W1477InputKeepsZeroIso",
      "w1489W1477InputKeepsOneIso",
      "w1489W1477InputKeepsLeftSrc",
      "w1489W1477InputKeepsRightSrc",
      "w1489W1477InputKeepsLeftFac",
      "w1489W1477InputKeepsRightFac",
      "w1489W1477InputKeepsZeroMap",
      "w1489W1477InputKeepsOneMap",
      "w1489W1477InputKeepsZeroMapFac",
      "w1489W1477InputKeepsOneMapFac",
      "w1489W1477InputKeepsLeftNaturality",
      "w1489W1477InputKeepsRightNaturality",
      "w1489W1477InputKeepsZeroMapId",
      "w1489W1477InputKeepsOneMapId",
      "w1489W1477InputKeepsZeroMapComp",
      "w1489W1477InputKeepsOneMapComp",
      "w1489W1477InputKeepsNormalizedLiftObjImage",
      "w1489W1477InputKeepsNormalizedLiftZeroMapImage",
      "w1489W1477InputKeepsNormalizedLiftOneMapImage",
      "w1489W1477InputKeepsTargetDifferenceSurjective",
      "w1489W1477InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1489W1477InputKeepsConstructedLocalizedRightAdjoint",
      "w1489LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1489TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1489FullDataKeepsConstructedBoundaryRelation",
      "w1489FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1489_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1489_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1489_count",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi1Input",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1489_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1489_count",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi2Input",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1489_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1489_count",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi3Input",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1489_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1489_count",
      "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsObjectImageInput",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1489_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1489_count",
      "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsRightAdjointInput",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1489_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1489_count",
      "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsTargetSurjectivityInput",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1489_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1489_count",
      "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsTargetCompactnessInput",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1489_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1489_count",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsMappedCokernelInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1489_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1489_count",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsEndpointClosedEmbeddingInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1489_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1489_count",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeClosedEmbeddingInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1489_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1489_count",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeCokernelTopInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1489_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1489_count",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeKernelEqualityInput",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionExpandsW1488InputCount",
            "w1489BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionExpandsW1477InputCount"]
  constructionResult :=
    "proved: W1489 reconstructs the normalized lift object-image law and\
      the localized right-adjoint functor fields, reconstructs target-difference\
      surjectivity from a preimage chooser and equation, reconstructs target\
      compactness from a nonbottom filter point chooser and equation,\
      reconstructs mapped explicit cokernel closed embeddings from embedding\
      and closed-range fields, reconstructs the first, second, and third\
      selected-difference closed-embedding components from embedding and\
      closed-range fields, reconstructs endpoint closed embeddings from\
      endpoint embedding and closed-range fields, reconstructs unit\
      mapping-cone closed embeddings from unit mapping-cone embedding and\
      closed-range fields, reconstructs the unit mapping-cone cokernel-top\
      family from preimage chooser and equation fields, reconstructs the unit\
      mapping-cone kernel equality from forward and backward implication\
      fields, then feeds those laws into W1477"
  projectionResult :=
    "proved: W1489's derived object-image law is used by the normalized lift\
      blueprint, its derived localized right adjoint is used by the W1477\
      input, and its target-difference preimage witness reconstructs the W1477\
      target-surjectivity provider while its target compactness point witness\
      reconstructs the W1477 compactness provider; the mapped cokernel\
      embedding and closed-range fields reconstruct the W1477 closed-embedding\
      provider; the first selected-difference embedding and closed-range\
      fields reconstruct the W1477 pi1 closed-embedding component; the second\
      selected-difference embedding and closed-range fields reconstruct the\
      W1477 pi2 closed-embedding component; the third selected-difference\
      embedding and closed-range fields reconstruct the W1477 pi3\
      closed-embedding component; the endpoint embedding and closed-range\
      fields reconstruct the W1477 endpoint closed-embedding family; the unit\
      mapping-cone embedding and closed-range fields reconstruct the W1477\
      unit mapping-cone closed-embedding family; the unit mapping-cone\
      preimage chooser and equation fields reconstruct the W1477 cokernel-top\
      family; the unit mapping-cone forward and backward implication fields\
      reconstruct the W1477 kernel equality family; W1477 preserves the\
      map-image, raw lift blueprint, localized-unit, boundary, and\
      target/endpoint projections; product success is still not claimed"
  objectImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1489
  componentObjectImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1489
  targetSurjectivityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1489
  componentTargetSurjectivityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1489
  targetCompactnessInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1489
  componentTargetCompactnessInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1489
  mappedCokernelInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1489
  componentMappedCokernelInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1489
  endpointClosedEmbeddingInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1489
  componentEndpointClosedEmbeddingInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1489
  unitMappingConeClosedEmbeddingInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1489
  componentUnitMappingConeClosedEmbeddingInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1489
  unitMappingConeCokernelTopInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1489
  componentUnitMappingConeCokernelTopInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1489
  unitMappingConeKernelEqualityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1489
  componentUnitMappingConeKernelEqualityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1489
  selectedDifferencePi1InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1489
  componentSelectedDifferencePi1InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1489
  selectedDifferencePi2InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1489
  componentSelectedDifferencePi2InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1489
  selectedDifferencePi3InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1489
  componentSelectedDifferencePi3InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1489
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1489
  productSuccessClaimed := false

theorem currentW1489W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionStateW1489.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
