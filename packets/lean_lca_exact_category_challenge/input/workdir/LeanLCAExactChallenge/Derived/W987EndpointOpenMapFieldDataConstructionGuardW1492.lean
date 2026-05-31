import LeanLCAExactChallenge.Derived.W987EndpointKernelEqualityFieldDataConstructionGuardW1491

/-!
W1492 refines W1491 by constructing the endpoint open-map family from the
unfolded image-openness field, while preserving the endpoint kernel-equality,
endpoint cokernel-top witness, unit mapping-cone cokernel-top, kernel-equality,
closed-embedding, endpoint closed-embedding, selected-difference,
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

/-- W1492 assembles one strict-preimage object datum from its constructor fields. -/
def normalizedLiftObjDataOfFieldsW1492
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

/-- W1492 assembles one strict-preimage map datum from its constructor fields. -/
def normalizedLiftMapDataOfFieldsW1492
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
      (normalizedLiftObjDataOfFieldsW1492 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Y)
      (normalizedLiftObjDataOfFieldsW1492 zeroSrc oneSrc zeroIso oneIso
        leftSrc rightSrc leftFac rightFac Z)
      τ where
  zeroMap := zeroMap τ
  oneMap := oneMap τ
  zero_fac := zeroMapFac τ
  one_fac := oneMapFac τ
  left_naturality := leftNaturality τ
  right_naturality := rightNaturality τ

/-- W1492 derives object-image normalization from object and arrow components. -/
def normalizedLiftObjImageOfFieldsW1492
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
    (normalizedLiftObjDataOfFieldsW1492 zeroSrc oneSrc zeroIso oneIso
      leftSrc rightSrc leftFac rightFac
      (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X := by
  refine CategoryTheory.Functor.ext (fun j => ?_) (fun _ _ f => ?_)
  · cases j
    · exact zeroObjImage X
    · exact oneObjImage X
  · cases f
    · simpa [normalizedLiftObjDataOfFieldsW1492,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        leftObjImage X
    · simpa [normalizedLiftObjDataOfFieldsW1492,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        rightObjImage X
    · simp

/-- W1492 packages raw localized right-adjoint functor fields. -/
def localizedRightAdjointFunctorFieldsOfRawW1492
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

/-- W1492 reconstructs the localized right-adjoint functor from raw fields. -/
def localizedRightAdjointOfRawW1492
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
    (localizedRightAdjointFunctorFieldsOfRawW1492 obj map mapId mapComp)

/-- W1492 builds target-difference surjectivity from a preimage chooser. -/
def targetDifferenceSurjectivePrimitiveOfWitnessW1492
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

/-- W1492 builds target-codomain compact no-univ membership from point witnesses. -/
def targetCodomainCompactNoUnivMembershipPrimitiveOfWitnessW1492
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

/-- W1492 builds mapped explicit cokernel closed embeddings from component fields. -/
def mappedExplicitCokernelClosedEmbeddingOfFieldsW1492
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

/-- W1492 builds endpoint closed embeddings from endpoint embedding and closed-range fields. -/
def endpointClosedEmbeddingOfFieldsW1492
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

/-- W1492 builds endpoint open-map facts from unfolded image-openness fields. -/
def endpointOpenMapOfImageOpenW1492
    (endpointOpenMapImageOpen :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
        (U : Set (K.sc i).X₂),
          IsOpen U →
            IsOpen (((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃) '' U))
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃) :=
  fun U hU => endpointOpenMapImageOpen K i U hU

/-- W1492 builds endpoint cokernel-top facts from surjectivity witnesses. -/
def endpointCokernelTopOfWitnessW1492
    (endpointCokernelPreimage :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
        (K.sc i).X₃ → (K.sc i).X₂)
    (endpointCokernelPreimage_eq :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
        (x₃ : (K.sc i).X₃),
          (K.sc i).g (endpointCokernelPreimage K i x₃) = x₃)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    MetrizableLCA.cokernelSubgroup (K.sc i).g = ⊤ :=
  MetrizableLCA.cokernelSubgroup_eq_top_of_surjective
    ((K.sc i).g) (by
      intro x₃
      exact ⟨endpointCokernelPreimage K i x₃,
        endpointCokernelPreimage_eq K i x₃⟩)

/-- W1492 builds endpoint kernel equalities from implication fields. -/
def endpointKernelEqualityOfFieldsW1492
    (endpointKernelForward :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
        (x₂ : (K.sc i).X₂),
          (K.sc i).g x₂ = 0 →
            ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂)
    (endpointKernelBackward :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
        (x₂ : (K.sc i).X₂),
          (∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂) →
            (K.sc i).g x₂ = 0)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
    (x₂ : (K.sc i).X₂) :
    (K.sc i).g x₂ = 0 ↔
      ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂ :=
  ⟨endpointKernelForward K i x₂,
    endpointKernelBackward K i x₂⟩

/-- W1492 builds unit mapping-cone closed embeddings from component fields. -/
def unitMappingConeClosedEmbeddingOfFieldsW1492
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

/-- W1492 builds unit mapping-cone cokernel-top facts from surjectivity witnesses. -/
def unitMappingConeCokernelTopOfWitnessW1492
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

/-- W1492 builds unit mapping-cone kernel equalities from implication fields. -/
def unitMappingConeKernelEqualityOfFieldsW1492
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

/-- W1492 builds the first selected-difference closed-embedding field from components. -/
def selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1492
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

/-- W1492 builds the second selected-difference closed-embedding field from components. -/
def selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1492
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

/-- W1492 builds the third selected-difference closed-embedding field from components. -/
def selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1492
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
W1492 keeps W1490's endpoint cokernel-top, unit mapping-cone cokernel-top,
kernel-equality, closed-embedding, endpoint closed-embedding,
selected-difference, mapped-cokernel, target-surjectivity, target-compactness,
normalized lift, and localized right-adjoint splits and replaces the endpoint
kernel-equality family by implication fields.
-/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492 :
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
      ((normalizedLiftMapDataOfFieldsW1492 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImageOfFieldsW1492 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
          normalizedLiftLeftObjImage normalizedLiftRightObjImage Y)).app WalkingParallelPair.zero =
      (eqToHom (normalizedLiftObjImageOfFieldsW1492 normalizedLiftZeroSrc
        normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
        normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
        normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
        normalizedLiftLeftObjImage normalizedLiftRightObjImage X) ≫ τ).app WalkingParallelPair.zero
  normalizedLiftOneMapImage :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      ((normalizedLiftMapDataOfFieldsW1492 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroMap normalizedLiftOneMap
          normalizedLiftZeroMapFac normalizedLiftOneMapFac
          normalizedLiftLeftNaturality normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (normalizedLiftObjImageOfFieldsW1492 normalizedLiftZeroSrc
          normalizedLiftOneSrc normalizedLiftZeroIso normalizedLiftOneIso
          normalizedLiftLeftSrc normalizedLiftRightSrc normalizedLiftLeftFac
          normalizedLiftRightFac normalizedLiftZeroObjImage normalizedLiftOneObjImage
          normalizedLiftLeftObjImage normalizedLiftRightObjImage Y)).app WalkingParallelPair.one =
      (eqToHom (normalizedLiftObjImageOfFieldsW1492 normalizedLiftZeroSrc
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
  endpointOpenMapImageOpen :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (U : Set (K.sc i).X₂),
        IsOpen U →
          IsOpen (((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃) '' U)
  endpointCokernelPreimage :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      (K.sc i).X₃ → (K.sc i).X₂
  endpointCokernelPreimage_eq :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₃ : (K.sc i).X₃),
        (K.sc i).g (endpointCokernelPreimage K i x₃) = x₃
  endpointKernelForward :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₂ : (K.sc i).X₂),
        (K.sc i).g x₂ = 0 →
          ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂
  endpointKernelBackward :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₂ : (K.sc i).X₂),
        (∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂) →
          (K.sc i).g x₂ = 0
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
          localizedRightAdjointOfRawW1492
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp).obj X
  boundedHomotopyLocalizedAdjunctionUnitNaturality :
    ∀ {X Y : BoundedComplexCategory MetrizableLCA.{0}} (f : X ⟶ Y),
      f ≫ boundedHomotopyLocalizedAdjunctionUnitApp Y =
        boundedHomotopyLocalizedAdjunctionUnitApp X ≫
          (boundedHomotopyLocalizedVerdierFunctorW1461 ⋙
            localizedRightAdjointOfRawW1492
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp).map f
  boundedHomotopyLocalizedAdjunctionCounitApp :
    ∀ Y : BoundedHomotopyLocalizedCategoryW1461,
      ((localizedRightAdjointOfRawW1492
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp) ⋙
        boundedHomotopyLocalizedVerdierFunctorW1461).obj Y ⟶
        Y
  boundedHomotopyLocalizedAdjunctionCounitNaturality :
    ∀ {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y),
      ((localizedRightAdjointOfRawW1492
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
          (localizedRightAdjointOfRawW1492
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
          (localizedRightAdjointOfRawW1492
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          boundedHomotopyLocalizedAdjunctionUnitApp
          boundedHomotopyLocalizedAdjunctionUnitNaturality
          boundedHomotopyLocalizedAdjunctionCounitApp
          boundedHomotopyLocalizedAdjunctionCounitNaturality).app Y =
        (NatTrans.id
          ((localizedRightAdjointOfRawW1492
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
          (localizedRightAdjointOfRawW1492
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfRawW1492
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
          (localizedRightAdjointOfRawW1492
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfRawW1492
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
          (localizedRightAdjointOfRawW1492
            boundedHomotopyLocalizedRightAdjointObj
            boundedHomotopyLocalizedRightAdjointMap
            boundedHomotopyLocalizedRightAdjointMapId
            boundedHomotopyLocalizedRightAdjointMapComp)
          (localizedAdjunctionUnitOfW1465
            (localizedRightAdjointOfRawW1492
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

/-- W1492 reconstructs the W718 selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
    where
  pi1 :=
    selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1492
      input.globalClosedEmbeddingPi1Embedding
      input.globalClosedEmbeddingPi1ClosedRange
  pi2 :=
    selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1492
      input.globalClosedEmbeddingPi2Embedding
      input.globalClosedEmbeddingPi2ClosedRange
  pi3 :=
    selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1492
      input.globalClosedEmbeddingPi3Embedding
      input.globalClosedEmbeddingPi3ClosedRange

/-- W1492 builds the W519 provider from embedding and closed-range fields. -/
def mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    MappedExplicitCokernelClosedEmbeddingProviderW519
    where
  isClosedEmbedding :=
    mappedExplicitCokernelClosedEmbeddingOfFieldsW1492
      input.mappedExplicitCokernelEmbedding
      input.mappedExplicitCokernelClosedRange

/-- W1492 builds the strict-preimage object-data family from its fields. -/
def normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y :=
  fun Y =>
    normalizedLiftObjDataOfFieldsW1492 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac Y

/-- W1492 builds the strict-preimage map-data family from its fields. -/
def normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input Y)
        (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input Z)
        τ :=
  fun {_Y _Z} τ =>
    normalizedLiftMapDataOfFieldsW1492 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroMap
      input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
      input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
      input.normalizedLiftRightNaturality τ

/-- W1492 derives the raw lift map identity law from zero/one component laws. -/
def normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input (𝟙 Y)).natTrans =
        𝟙 (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input Y).diagram :=
  fun Y => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492,
        normalizedLiftObjDataOfFieldsW1492,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492,
        normalizedLiftMapDataOfFieldsW1492,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapId Y
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492,
        normalizedLiftObjDataOfFieldsW1492,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492,
        normalizedLiftMapDataOfFieldsW1492,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapId Y

/-- W1492 derives the raw lift map composition law from zero/one component laws. -/
def normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input (τ ≫ σ)).natTrans =
        (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input τ).natTrans ≫
          (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
            input σ).natTrans :=
  fun {_Y _Z _T} τ σ => by
    apply NatTrans.ext
    funext j
    cases j
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492,
        normalizedLiftObjDataOfFieldsW1492,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492,
        normalizedLiftMapDataOfFieldsW1492,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftZeroMapComp τ σ
    · simpa [normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492,
        normalizedLiftObjDataOfFieldsW1492,
        normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492,
        normalizedLiftMapDataOfFieldsW1492,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans,
        Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram] using
        input.normalizedLiftOneMapComp τ σ

/-- W1492 derives the normalized lift object-image law from four components. -/
def normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (normalizedLiftObjDataOfFieldsW1492 input.normalizedLiftZeroSrc
        input.normalizedLiftOneSrc input.normalizedLiftZeroIso
        input.normalizedLiftOneIso input.normalizedLiftLeftSrc
        input.normalizedLiftRightSrc input.normalizedLiftLeftFac
        input.normalizedLiftRightFac
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X :=
  fun X =>
    normalizedLiftObjImageOfFieldsW1492 input.normalizedLiftZeroSrc
      input.normalizedLiftOneSrc input.normalizedLiftZeroIso
      input.normalizedLiftOneIso input.normalizedLiftLeftSrc
      input.normalizedLiftRightSrc input.normalizedLiftLeftFac
      input.normalizedLiftRightFac input.normalizedLiftZeroObjImage
      input.normalizedLiftOneObjImage input.normalizedLiftLeftObjImage
      input.normalizedLiftRightObjImage X

/-- W1492 derives the normalized lift map-image law from zero/one components. -/
def normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
      (τ : X ⟶ Y),
      (normalizedLiftMapDataOfFieldsW1492 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
            input Y) =
      eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
            input X) ≫ τ :=
  fun {_X _Y} τ => by
    apply NatTrans.ext
    funext j
    cases j
    · exact input.normalizedLiftZeroMapImage τ
    · exact input.normalizedLiftOneMapImage τ

/-- W1492 builds the raw lift blueprint from its object and functorial fields. -/
def normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData :=
    normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input
  mapData :=
    normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input
  map_id :=
    normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input
  map_comp :=
    normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input

/-- W1492 builds the normalized lift blueprint from the raw lift fields. -/
def normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint :=
    normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input
  obj_image :=
    normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input
  map_image :=
    normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input

/-- W1492 builds W973 closed-embedding closedness data from the raw W519 field. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input

/-- W1492 reconstructs the localized right-adjoint functor fields. -/
def boundedHomotopyLocalizedRightAdjointFieldsOfW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    LocalizedRightAdjointFunctorFieldsW1467 :=
  localizedRightAdjointFunctorFieldsOfRawW1492
    input.boundedHomotopyLocalizedRightAdjointObj
    input.boundedHomotopyLocalizedRightAdjointMap
    input.boundedHomotopyLocalizedRightAdjointMapId
    input.boundedHomotopyLocalizedRightAdjointMapComp

/-- W1492 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    (boundedHomotopyLocalizedRightAdjointFieldsOfW1492 input)

/-- W1492's reconstructed right-adjoint field package keeps the object map. -/
theorem w1492LocalizedRightAdjointFieldsKeepObj
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : BoundedHomotopyLocalizedCategoryW1461) :
    (boundedHomotopyLocalizedRightAdjointFieldsOfW1492 input).obj X =
      input.boundedHomotopyLocalizedRightAdjointObj X :=
  rfl

/-- W1492's reconstructed right-adjoint field package keeps the morphism map. -/
theorem w1492LocalizedRightAdjointFieldsKeepMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y) :
    (boundedHomotopyLocalizedRightAdjointFieldsOfW1492 input).map f =
      input.boundedHomotopyLocalizedRightAdjointMap f :=
  rfl

/-- W1492's reconstructed right adjoint keeps the object map. -/
theorem w1492LocalizedRightAdjointKeepsObj
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : BoundedHomotopyLocalizedCategoryW1461) :
    (boundedHomotopyLocalizedRightAdjointOfW1492 input).obj X =
      input.boundedHomotopyLocalizedRightAdjointObj X :=
  rfl

/-- W1492's reconstructed right adjoint keeps the morphism map. -/
theorem w1492LocalizedRightAdjointKeepsMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : BoundedHomotopyLocalizedCategoryW1461} (f : X ⟶ Y) :
    (boundedHomotopyLocalizedRightAdjointOfW1492 input).map f =
      input.boundedHomotopyLocalizedRightAdjointMap f :=
  rfl

/-- W1492 reconstructs the target-difference surjectivity provider. -/
def targetDifferenceSurjectiveForTargetProviderOfW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y :=
  targetDifferenceSurjectivePrimitiveOfWitnessW1492
    input.targetDifferenceSurjectivePreimage
    input.targetDifferenceSurjectivePreimageSpec

/-- W1492 reconstructs the target-codomain compact no-univ membership provider. -/
def targetCodomainCompactNoUnivMembershipProviderOfW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y :=
  targetCodomainCompactNoUnivMembershipPrimitiveOfWitnessW1492
    input.targetCodomainCompactMeetPoint
    input.targetCodomainCompactMeetSpec

/-- W1492's target-difference witness field satisfies the selected preimage equation. -/
theorem w1492TargetDifferenceSurjectiveWitnessSpec
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    (y : wppOpCodomainW441 Y) :
    (((wppOpLeftW441 Y - wppOpRightW441 Y) :
      wppOpDomainW441 Y ⟶ wppOpCodomainW441 Y) :
      wppOpDomainW441 Y → wppOpCodomainW441 Y)
      (input.targetDifferenceSurjectivePreimage Y y) = y :=
  input.targetDifferenceSurjectivePreimageSpec Y y

/-- W1492's compactness witness field satisfies the selected neighbourhood-meet equation. -/
theorem w1492TargetCodomainCompactWitnessSpec
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    {f : Filter (wppOpCodomainW441 Y)} (hf : f ≠ ⊥) :
    (𝓝 (input.targetCodomainCompactMeetPoint Y (f := f) hf) ⊓ f) ≠ ⊥ :=
  input.targetCodomainCompactMeetSpec Y (f := f) hf

/-- W1492 builds the W1477 input after reconstructing the map-data family. -/
def w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    W987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputW1477 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    targetDifferenceSurjectiveForTargetProviderOfW1492 input
  targetCodomainCompactNoUnivMembershipProvider :=
    targetCodomainCompactNoUnivMembershipProviderOfW1492 input
  globalClosedEmbeddingPi1 :=
    selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1492
      input.globalClosedEmbeddingPi1Embedding
      input.globalClosedEmbeddingPi1ClosedRange
  globalClosedEmbeddingPi2 :=
    selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1492
      input.globalClosedEmbeddingPi2Embedding
      input.globalClosedEmbeddingPi2ClosedRange
  globalClosedEmbeddingPi3 :=
    selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1492
      input.globalClosedEmbeddingPi3Embedding
      input.globalClosedEmbeddingPi3ClosedRange
  mappedExplicitCokernelClosedEmbedding :=
    mappedExplicitCokernelClosedEmbeddingOfFieldsW1492
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
    normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input
  normalizedLiftZeroMapImage := input.normalizedLiftZeroMapImage
  normalizedLiftOneMapImage := input.normalizedLiftOneMapImage
  targetFixedTargetUniq := input.targetFixedTargetUniq
  localizationModelFixedTargetUniq := input.localizationModelFixedTargetUniq
  sourcePretriangulated := input.sourcePretriangulated
  sourceTriangulated := input.sourceTriangulated
  triangleCompletion := input.triangleCompletion
  endpointClosedEmbedding :=
    endpointClosedEmbeddingOfFieldsW1492
      input.endpointEmbedding
      input.endpointClosedRange
  endpointOpenMap :=
    endpointOpenMapOfImageOpenW1492
      input.endpointOpenMapImageOpen
  endpointCokernelTop :=
    endpointCokernelTopOfWitnessW1492
      input.endpointCokernelPreimage
      input.endpointCokernelPreimage_eq
  endpointKernelEquality :=
    endpointKernelEqualityOfFieldsW1492
      input.endpointKernelForward
      input.endpointKernelBackward
  boundedHomotopyLocalizedRightAdjointFields :=
    boundedHomotopyLocalizedRightAdjointFieldsOfW1492 input
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
    unitMappingConeClosedEmbeddingOfFieldsW1492
      input.unitMappingConeModel
      input.unitMappingConeEmbedding
      input.unitMappingConeClosedRange
  unitMappingConeOpenMap := input.unitMappingConeOpenMap
  unitMappingConeCokernelTop :=
    unitMappingConeCokernelTopOfWitnessW1492
      input.unitMappingConeModel
      input.unitMappingConeCokernelPreimage
      input.unitMappingConeCokernelPreimage_eq
  unitMappingConeKernelEquality :=
    unitMappingConeKernelEqualityOfFieldsW1492
      input.unitMappingConeModel
      input.unitMappingConeKernelForward
      input.unitMappingConeKernelBackward
  unitMappingConeIsoHom := input.unitMappingConeIsoHom
  unitMappingConeIsoInv := input.unitMappingConeIsoInv
  unitMappingConeIsoHomInvId := input.unitMappingConeIsoHomInvId
  unitMappingConeIsoInvHomId := input.unitMappingConeIsoInvHomId

/-- W1492 builds W945 localized-unit data through W1477. -/
def localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input)

/-- W1492 builds W730 boundary/relation data through W1477. -/
def boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input)

/-- W1492 builds W986 target/endpoint data through W1477. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input)

/-- W1492 builds W987 full data through W1477. -/
noncomputable def fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
      input)

/-- W1492's first selected-difference closed embedding keeps the embedding field. -/
theorem w1492SelectedDifferenceClosedEmbeddingPi1KeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi1Embedding
        input.globalClosedEmbeddingPi1ClosedRange S).toIsEmbedding =
      input.globalClosedEmbeddingPi1Embedding S :=
  rfl

/-- W1492's first selected-difference closed embedding keeps the closed-range field. -/
theorem w1492SelectedDifferenceClosedEmbeddingPi1KeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi1Embedding
        input.globalClosedEmbeddingPi1ClosedRange S).isClosed_range =
      input.globalClosedEmbeddingPi1ClosedRange S :=
  rfl

/-- W1492's constructed W718 provider keeps the reconstructed first component field. -/
theorem w1492GlobalClosedEmbeddingComponentsKeepsConstructedPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi1Embedding
        input.globalClosedEmbeddingPi1ClosedRange :=
  rfl

/-- W1492's second selected-difference closed embedding keeps the embedding field. -/
theorem w1492SelectedDifferenceClosedEmbeddingPi2KeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi2Embedding
        input.globalClosedEmbeddingPi2ClosedRange S).toIsEmbedding =
      input.globalClosedEmbeddingPi2Embedding S :=
  rfl

/-- W1492's second selected-difference closed embedding keeps the closed-range field. -/
theorem w1492SelectedDifferenceClosedEmbeddingPi2KeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi2Embedding
        input.globalClosedEmbeddingPi2ClosedRange S).isClosed_range =
      input.globalClosedEmbeddingPi2ClosedRange S :=
  rfl

/-- W1492's constructed W718 provider keeps the reconstructed second component field. -/
theorem w1492GlobalClosedEmbeddingComponentsKeepsConstructedPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi2Embedding
        input.globalClosedEmbeddingPi2ClosedRange :=
  rfl

/-- W1492's third selected-difference closed embedding keeps the embedding field. -/
theorem w1492SelectedDifferenceClosedEmbeddingPi3KeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi3Embedding
        input.globalClosedEmbeddingPi3ClosedRange S).toIsEmbedding =
      input.globalClosedEmbeddingPi3Embedding S :=
  rfl

/-- W1492's third selected-difference closed embedding keeps the closed-range field. -/
theorem w1492SelectedDifferenceClosedEmbeddingPi3KeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi3Embedding
        input.globalClosedEmbeddingPi3ClosedRange S).isClosed_range =
      input.globalClosedEmbeddingPi3ClosedRange S :=
  rfl

/-- W1492's constructed W718 provider keeps the reconstructed third component field. -/
theorem w1492GlobalClosedEmbeddingComponentsKeepsConstructedPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi3Embedding
        input.globalClosedEmbeddingPi3ClosedRange :=
  rfl

/-- W1492's constructed W973 data keeps the constructed W718 provider. -/
theorem w1492ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input :=
  rfl

/-- W1492's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1492ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input :=
  rfl

/-- W1492's reconstructed closed embedding keeps the embedding field. -/
theorem w1492MappedExplicitCokernelClosedEmbeddingKeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedExplicitCokernelClosedEmbeddingOfFieldsW1492
        input.mappedExplicitCokernelEmbedding
        input.mappedExplicitCokernelClosedRange f).toIsEmbedding =
      input.mappedExplicitCokernelEmbedding f :=
  rfl

/-- W1492's reconstructed closed embedding keeps the closed-range field. -/
theorem w1492MappedExplicitCokernelClosedEmbeddingKeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedExplicitCokernelClosedEmbeddingOfFieldsW1492
        input.mappedExplicitCokernelEmbedding
        input.mappedExplicitCokernelClosedRange f).isClosed_range =
      input.mappedExplicitCokernelClosedRange f :=
  rfl

/-- W1492's constructed W519 provider keeps the reconstructed closed embedding. -/
theorem w1492MappedCokernelClosedEmbeddingProviderKeepsConstructedField
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).isClosedEmbedding f =
      mappedExplicitCokernelClosedEmbeddingOfFieldsW1492
        input.mappedExplicitCokernelEmbedding
        input.mappedExplicitCokernelClosedRange f :=
  rfl

/-- W1492's endpoint closed embedding keeps the embedding field. -/
theorem w1492EndpointClosedEmbeddingKeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    (endpointClosedEmbeddingOfFieldsW1492
        input.endpointEmbedding input.endpointClosedRange K i).toIsEmbedding =
      input.endpointEmbedding K i :=
  rfl

/-- W1492's endpoint closed embedding keeps the closed-range field. -/
theorem w1492EndpointClosedEmbeddingKeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    (endpointClosedEmbeddingOfFieldsW1492
        input.endpointEmbedding input.endpointClosedRange K i).isClosed_range =
      input.endpointClosedRange K i :=
  rfl

/-- W1492's endpoint open-map construction keeps the unfolded image-openness field. -/
theorem w1492EndpointOpenMapKeepsImageOpen
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
    (U : Set (K.sc i).X₂) (hU : IsOpen U) :
    (endpointOpenMapOfImageOpenW1492
        input.endpointOpenMapImageOpen K i) U hU =
      input.endpointOpenMapImageOpen K i U hU :=
  rfl

/-- W1492's endpoint cokernel-top witness gives surjectivity. -/
theorem w1492EndpointCokernelTopWitnessSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ) :
    Function.Surjective ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃) := by
  intro x₃
  exact ⟨input.endpointCokernelPreimage K i x₃,
    input.endpointCokernelPreimage_eq K i x₃⟩

/-- W1492's endpoint cokernel-top witness keeps its equation field. -/
theorem w1492EndpointCokernelTopWitnessSpec
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
    (x₃ : (K.sc i).X₃) :
    (K.sc i).g (input.endpointCokernelPreimage K i x₃) = x₃ :=
  input.endpointCokernelPreimage_eq K i x₃

/-- W1492's endpoint kernel equality keeps the forward implication. -/
theorem w1492EndpointKernelEqualityKeepsForward
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
    (x₂ : (K.sc i).X₂)
    (h : (K.sc i).g x₂ = 0) :
    (endpointKernelEqualityOfFieldsW1492
        input.endpointKernelForward
        input.endpointKernelBackward K i x₂).mp h =
      input.endpointKernelForward K i x₂ h :=
  rfl

/-- W1492's endpoint kernel equality keeps the backward implication. -/
theorem w1492EndpointKernelEqualityKeepsBackward
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
    (x₂ : (K.sc i).X₂)
    (h : ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂) :
    (endpointKernelEqualityOfFieldsW1492
        input.endpointKernelForward
        input.endpointKernelBackward K i x₂).mpr h =
      input.endpointKernelBackward K i x₂ h :=
  rfl

/-- W1492's unit mapping-cone closed embedding keeps the embedding field. -/
theorem w1492UnitMappingConeClosedEmbeddingKeepsEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    (unitMappingConeClosedEmbeddingOfFieldsW1492
        input.unitMappingConeModel input.unitMappingConeEmbedding
        input.unitMappingConeClosedRange X i).toIsEmbedding =
      input.unitMappingConeEmbedding X i :=
  rfl

/-- W1492's unit mapping-cone closed embedding keeps the closed-range field. -/
theorem w1492UnitMappingConeClosedEmbeddingKeepsClosedRange
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    (unitMappingConeClosedEmbeddingOfFieldsW1492
        input.unitMappingConeModel input.unitMappingConeEmbedding
        input.unitMappingConeClosedRange X i).isClosed_range =
      input.unitMappingConeClosedRange X i :=
  rfl

/-- W1492's unit mapping-cone cokernel-top witness gives surjectivity. -/
theorem w1492UnitMappingConeCokernelTopWitnessSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ) :
    Function.Surjective (((input.unitMappingConeModel X).as.sc i).g :
      ((input.unitMappingConeModel X).as.sc i).X₂ →
        ((input.unitMappingConeModel X).as.sc i).X₃) := by
  intro x₃
  exact ⟨input.unitMappingConeCokernelPreimage X i x₃,
    input.unitMappingConeCokernelPreimage_eq X i x₃⟩

/-- W1492's unit mapping-cone cokernel-top witness keeps its equation field. -/
theorem w1492UnitMappingConeCokernelTopWitnessSpec
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
    (x₃ : ((input.unitMappingConeModel X).as.sc i).X₃) :
    ((input.unitMappingConeModel X).as.sc i).g
        (input.unitMappingConeCokernelPreimage X i x₃) =
      x₃ :=
  input.unitMappingConeCokernelPreimage_eq X i x₃

/-- W1492's unit mapping-cone kernel equality keeps the forward implication. -/
theorem w1492UnitMappingConeKernelEqualityKeepsForward
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
    (x₂ : ((input.unitMappingConeModel X).as.sc i).X₂)
    (h : ((input.unitMappingConeModel X).as.sc i).g x₂ = 0) :
    (unitMappingConeKernelEqualityOfFieldsW1492
        input.unitMappingConeModel
        input.unitMappingConeKernelForward
        input.unitMappingConeKernelBackward X i x₂).mp h =
      input.unitMappingConeKernelForward X i x₂ h :=
  rfl

/-- W1492's unit mapping-cone kernel equality keeps the backward implication. -/
theorem w1492UnitMappingConeKernelEqualityKeepsBackward
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
    (x₂ : ((input.unitMappingConeModel X).as.sc i).X₂)
    (h :
      ∃ x₁ : ((input.unitMappingConeModel X).as.sc i).X₁,
        ((input.unitMappingConeModel X).as.sc i).f x₁ = x₂) :
    (unitMappingConeKernelEqualityOfFieldsW1492
        input.unitMappingConeModel
        input.unitMappingConeKernelForward
        input.unitMappingConeKernelBackward X i x₂).mpr h =
      input.unitMappingConeKernelBackward X i x₂ h :=
  rfl

/-- W1492's object-data family keeps the zero object field. -/
theorem w1492NormalizedLiftObjDataKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input Y).zeroSrc =
      input.normalizedLiftZeroSrc Y :=
  rfl

/-- W1492's object-data family keeps the one object field. -/
theorem w1492NormalizedLiftObjDataKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input Y).oneSrc =
      input.normalizedLiftOneSrc Y :=
  rfl

/-- W1492's object-data family keeps the zero comparison isomorphism. -/
theorem w1492NormalizedLiftObjDataKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input Y).zeroIso =
      input.normalizedLiftZeroIso Y :=
  rfl

/-- W1492's object-data family keeps the one comparison isomorphism. -/
theorem w1492NormalizedLiftObjDataKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input Y).oneIso =
      input.normalizedLiftOneIso Y :=
  rfl

/-- W1492's object-data family keeps the left source map. -/
theorem w1492NormalizedLiftObjDataKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input Y).leftSrc =
      input.normalizedLiftLeftSrc Y :=
  rfl

/-- W1492's object-data family keeps the right source map. -/
theorem w1492NormalizedLiftObjDataKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input Y).rightSrc =
      input.normalizedLiftRightSrc Y :=
  rfl

/-- W1492's object-data family keeps the left factorization law. -/
theorem w1492NormalizedLiftObjDataKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input Y).left_fac =
      input.normalizedLiftLeftFac Y :=
  rfl

/-- W1492's object-data family keeps the right factorization law. -/
theorem w1492NormalizedLiftObjDataKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input Y).right_fac =
      input.normalizedLiftRightFac Y :=
  rfl

/-- W1492's map-data family keeps the zero map field. -/
theorem w1492NormalizedLiftMapDataKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input τ).zeroMap =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1492's map-data family keeps the one map field. -/
theorem w1492NormalizedLiftMapDataKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input τ).oneMap =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1492's map-data family keeps the zero-map factorization law. -/
theorem w1492NormalizedLiftMapDataKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input τ).zero_fac =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1492's map-data family keeps the one-map factorization law. -/
theorem w1492NormalizedLiftMapDataKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input τ).one_fac =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1492's map-data family keeps the left naturality law. -/
theorem w1492NormalizedLiftMapDataKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input τ).left_naturality =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1492's map-data family keeps the right naturality law. -/
theorem w1492NormalizedLiftMapDataKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input τ).right_naturality =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1492's raw lift blueprint keeps the constructed object-data family. -/
theorem w1492NormalizedLiftRawBlueprintKeepsConstructedObjData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).objData =
      normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input :=
  rfl

/-- W1492's raw lift blueprint keeps the constructed map-data family. -/
theorem w1492NormalizedLiftRawBlueprintKeepsConstructedMapData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).mapData τ =
      normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input τ :=
  rfl

/-- W1492's raw lift blueprint keeps the constructed identity law. -/
theorem w1492NormalizedLiftRawBlueprintKeepsMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).map_id Y =
      normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input Y :=
  rfl

/-- W1492's raw lift blueprint keeps the constructed composition law. -/
theorem w1492NormalizedLiftRawBlueprintKeepsMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).map_comp τ σ =
      normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input τ σ :=
  rfl

/-- W1492's normalized lift blueprint keeps the constructed raw lift blueprint. -/
theorem w1492NormalizedLiftBlueprintKeepsConstructedRawBlueprint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).blueprint =
      normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input :=
  rfl

/-- W1492's normalized lift blueprint keeps the object-image normalization field. -/
theorem w1492NormalizedLiftBlueprintKeepsObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).obj_image X =
      normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input X :=
  rfl

/-- W1492's normalized lift blueprint keeps the map-image normalization field. -/
theorem w1492NormalizedLiftBlueprintKeepsMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).map_image τ =
      normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input τ :=
  rfl

/-- W1492's input keeps the zero component map-image normalization law. -/
theorem w1492NormalizedLiftMapImageKeepsZeroComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1492 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
            input Y)).app WalkingParallelPair.zero =
      (eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
            input X) ≫ τ).app WalkingParallelPair.zero := by
  simpa [normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492]
    using input.normalizedLiftZeroMapImage τ

/-- W1492's input keeps the one component map-image normalization law. -/
theorem w1492NormalizedLiftMapImageKeepsOneComponent
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    ((normalizedLiftMapDataOfFieldsW1492 input.normalizedLiftZeroSrc
          input.normalizedLiftOneSrc input.normalizedLiftZeroIso
          input.normalizedLiftOneIso input.normalizedLiftLeftSrc
          input.normalizedLiftRightSrc input.normalizedLiftLeftFac
          input.normalizedLiftRightFac input.normalizedLiftZeroMap
          input.normalizedLiftOneMap input.normalizedLiftZeroMapFac
          input.normalizedLiftOneMapFac input.normalizedLiftLeftNaturality
          input.normalizedLiftRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
            input Y)).app WalkingParallelPair.one =
      (eqToHom
          (normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
            input X) ≫ τ).app WalkingParallelPair.one := by
  simpa [normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492]
    using input.normalizedLiftOneMapImage τ

/-- W1492's W1477 input keeps the reconstructed first W718 component field. -/
theorem w1492W1477InputKeepsConstructedGlobalClosedEmbeddingPi1
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).globalClosedEmbeddingPi1 =
      selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi1Embedding
        input.globalClosedEmbeddingPi1ClosedRange :=
  rfl

/-- W1492's W1477 input keeps the reconstructed second W718 component field. -/
theorem w1492W1477InputKeepsConstructedGlobalClosedEmbeddingPi2
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).globalClosedEmbeddingPi2 =
      selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi2Embedding
        input.globalClosedEmbeddingPi2ClosedRange :=
  rfl

/-- W1492's W1477 input keeps the reconstructed third W718 component field. -/
theorem w1492W1477InputKeepsConstructedGlobalClosedEmbeddingPi3
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).globalClosedEmbeddingPi3 =
      selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1492
        input.globalClosedEmbeddingPi3Embedding
        input.globalClosedEmbeddingPi3ClosedRange :=
  rfl

/-- W1492's W1477 input keeps W519 mapped-cokernel data. -/
theorem w1492W1477InputKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageMapImageFieldDataW1477
        (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      mappedCokernelClosedEmbeddingProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input :=
  rfl

/-- W1492's W1477 input keeps the reconstructed endpoint closed-embedding family. -/
theorem w1492W1477InputKeepsConstructedEndpointClosedEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).endpointClosedEmbedding =
      endpointClosedEmbeddingOfFieldsW1492
        input.endpointEmbedding
        input.endpointClosedRange :=
  rfl

/-- W1492's W1477 input keeps the reconstructed endpoint open-map family. -/
theorem w1492W1477InputKeepsConstructedEndpointOpenMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).endpointOpenMap =
      endpointOpenMapOfImageOpenW1492
        input.endpointOpenMapImageOpen :=
  rfl

/-- W1492's W1477 input keeps the reconstructed endpoint cokernel-top family. -/
theorem w1492W1477InputKeepsConstructedEndpointCokernelTop
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).endpointCokernelTop =
      endpointCokernelTopOfWitnessW1492
        input.endpointCokernelPreimage
        input.endpointCokernelPreimage_eq :=
  rfl

/-- W1492's W1477 input keeps the reconstructed endpoint kernel equality. -/
theorem w1492W1477InputKeepsConstructedEndpointKernelEquality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).endpointKernelEquality =
      endpointKernelEqualityOfFieldsW1492
        input.endpointKernelForward
        input.endpointKernelBackward :=
  rfl

/-- W1492's W1477 input keeps the reconstructed unit mapping-cone closed-embedding family. -/
theorem w1492W1477InputKeepsConstructedUnitMappingConeClosedEmbedding
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).unitMappingConeClosedEmbedding =
      unitMappingConeClosedEmbeddingOfFieldsW1492
        input.unitMappingConeModel
        input.unitMappingConeEmbedding
      input.unitMappingConeClosedRange :=
  rfl

/-- W1492's W1477 input keeps the reconstructed unit mapping-cone cokernel-top family. -/
theorem w1492W1477InputKeepsConstructedUnitMappingConeCokernelTop
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).unitMappingConeCokernelTop =
      unitMappingConeCokernelTopOfWitnessW1492
        input.unitMappingConeModel
        input.unitMappingConeCokernelPreimage
        input.unitMappingConeCokernelPreimage_eq :=
  rfl

/-- W1492's W1477 input keeps the reconstructed unit mapping-cone kernel equality. -/
theorem w1492W1477InputKeepsConstructedUnitMappingConeKernelEquality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).unitMappingConeKernelEquality =
      unitMappingConeKernelEqualityOfFieldsW1492
        input.unitMappingConeModel
        input.unitMappingConeKernelForward
        input.unitMappingConeKernelBackward :=
  rfl

/-- W1492's W1477 input keeps the zero source object field. -/
theorem w1492W1477InputKeepsZeroSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftZeroSrc =
      input.normalizedLiftZeroSrc :=
  rfl

/-- W1492's W1477 input keeps the one source object field. -/
theorem w1492W1477InputKeepsOneSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftOneSrc =
      input.normalizedLiftOneSrc :=
  rfl

/-- W1492's W1477 input keeps the zero comparison isomorphism. -/
theorem w1492W1477InputKeepsZeroIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftZeroIso =
      input.normalizedLiftZeroIso :=
  rfl

/-- W1492's W1477 input keeps the one comparison isomorphism. -/
theorem w1492W1477InputKeepsOneIso
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftOneIso =
      input.normalizedLiftOneIso :=
  rfl

/-- W1492's W1477 input keeps the left source map. -/
theorem w1492W1477InputKeepsLeftSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftLeftSrc =
      input.normalizedLiftLeftSrc :=
  rfl

/-- W1492's W1477 input keeps the right source map. -/
theorem w1492W1477InputKeepsRightSrc
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftRightSrc =
      input.normalizedLiftRightSrc :=
  rfl

/-- W1492's W1477 input keeps the left factorization law. -/
theorem w1492W1477InputKeepsLeftFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftLeftFac =
      input.normalizedLiftLeftFac :=
  rfl

/-- W1492's W1477 input keeps the right factorization law. -/
theorem w1492W1477InputKeepsRightFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftRightFac =
      input.normalizedLiftRightFac :=
  rfl

/-- W1492's W1477 input keeps the zero map field. -/
theorem w1492W1477InputKeepsZeroMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftZeroMap τ =
      input.normalizedLiftZeroMap τ :=
  rfl

/-- W1492's W1477 input keeps the one map field. -/
theorem w1492W1477InputKeepsOneMap
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftOneMap τ =
      input.normalizedLiftOneMap τ :=
  rfl

/-- W1492's W1477 input keeps the zero-map factorization law. -/
theorem w1492W1477InputKeepsZeroMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftZeroMapFac τ =
      input.normalizedLiftZeroMapFac τ :=
  rfl

/-- W1492's W1477 input keeps the one-map factorization law. -/
theorem w1492W1477InputKeepsOneMapFac
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftOneMapFac τ =
      input.normalizedLiftOneMapFac τ :=
  rfl

/-- W1492's W1477 input keeps the left naturality law. -/
theorem w1492W1477InputKeepsLeftNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftLeftNaturality τ =
      input.normalizedLiftLeftNaturality τ :=
  rfl

/-- W1492's W1477 input keeps the right naturality law. -/
theorem w1492W1477InputKeepsRightNaturality
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftRightNaturality τ =
      input.normalizedLiftRightNaturality τ :=
  rfl

/-- W1492's W1477 input keeps the zero-map identity law. -/
theorem w1492W1477InputKeepsZeroMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftZeroMapId Y =
      input.normalizedLiftZeroMapId Y :=
  rfl

/-- W1492's W1477 input keeps the one-map identity law. -/
theorem w1492W1477InputKeepsOneMapId
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftOneMapId Y =
      input.normalizedLiftOneMapId Y :=
  rfl

/-- W1492's W1477 input keeps the zero-map composition law. -/
theorem w1492W1477InputKeepsZeroMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftZeroMapComp τ σ =
      input.normalizedLiftZeroMapComp τ σ :=
  rfl

/-- W1492's W1477 input keeps the one-map composition law. -/
theorem w1492W1477InputKeepsOneMapComp
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (τ : Y ⟶ Z) (σ : Z ⟶ T) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftOneMapComp τ σ =
      input.normalizedLiftOneMapComp τ σ :=
  rfl

/-- W1492's W1477 input keeps the object-image normalization field. -/
theorem w1492W1477InputKeepsNormalizedLiftObjImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftObjImage X =
      normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input X :=
  rfl

/-- W1492's W1477 input keeps the zero-component map-image normalization field. -/
theorem w1492W1477InputKeepsNormalizedLiftZeroMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftZeroMapImage τ =
      input.normalizedLiftZeroMapImage τ :=
  rfl

/-- W1492's W1477 input keeps the one-component map-image normalization field. -/
theorem w1492W1477InputKeepsNormalizedLiftOneMapImage
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492)
    {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (τ : X ⟶ Y) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).normalizedLiftOneMapImage τ =
      input.normalizedLiftOneMapImage τ :=
  rfl

/-- W1492's W1477 input keeps target-difference surjectivity. -/
theorem w1492W1477InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).targetDifferenceSurjectiveForTargetProvider =
      targetDifferenceSurjectiveForTargetProviderOfW1492 input :=
  rfl

/-- W1492's W1477 input keeps target-codomain compact no-univ membership. -/
theorem w1492W1477InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input).targetCodomainCompactNoUnivMembershipProvider =
      targetCodomainCompactNoUnivMembershipProviderOfW1492 input :=
  rfl

/-- W1492's W1477 input keeps the reconstructed localized right adjoint. -/
theorem w1492W1477InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    boundedHomotopyLocalizedRightAdjointOfW1477
        (w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1492 input :=
  rfl

/-- W1492's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1492LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1492 input :=
  rfl

/-- W1492's W986 construction keeps the constructed W973 closedness data. -/
theorem w1492TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input :=
  rfl

/-- W1492's constructed W987 provider projects to the constructed W730 data. -/
theorem w1492FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input :=
  rfl

/-- W1492's constructed W987 provider projects to the constructed W986 data. -/
theorem w1492FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492
        input :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492 :
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
    "endpoint open-map image-openness family",
    "endpoint cokernel preimage chooser family",
    "endpoint cokernel preimage equation family",
    "endpoint kernel forward implication family",
    "endpoint kernel backward implication family",
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

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492_count :
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492.length =
        74 :=
    rfl

/-- W1492 records the bundled first selected-difference closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1492 :
    List String :=
  ["first selected-difference closed-embedding diagram component field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component first selected-difference closed-embedding inputs. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1492 :
    List String :=
  ["first selected-difference closed-embedding diagram embedding field",
    "first selected-difference closed-embedding diagram closed-range field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one first selected-difference closed-embedding field by component fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi1Input :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1492_count]
  decide

/-- W1492 records the bundled second selected-difference closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1492 :
    List String :=
  ["second selected-difference closed-embedding diagram component field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component second selected-difference closed-embedding inputs. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1492 :
    List String :=
  ["second selected-difference closed-embedding diagram embedding field",
    "second selected-difference closed-embedding diagram closed-range field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one second selected-difference closed-embedding field by component fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi2Input :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1492_count]
  decide

/-- W1492 records the bundled third selected-difference closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1492 :
    List String :=
  ["third selected-difference closed-embedding diagram component field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component third selected-difference closed-embedding inputs. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1492 :
    List String :=
  ["third selected-difference closed-embedding diagram embedding field",
    "third selected-difference closed-embedding diagram closed-range field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one third selected-difference closed-embedding field by component fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi3Input :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1492_count]
  decide

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1492 :
    List String :=
  ["normalized lift object-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1492.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1492 :
    List String :=
  ["normalized lift zero object-image normalization",
    "normalized lift one object-image normalization",
    "normalized lift left arrow-image normalization",
    "normalized lift right arrow-image normalization"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1492.length =
      4 :=
  rfl

/-- W1492 replaces one object-image law by four component image laws. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsObjectImageInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1492_count]
  decide

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1492 :
    List String :=
  ["bounded homotopy localized right-adjoint functor field package"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1492.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1492 :
    List String :=
  ["bounded homotopy localized right-adjoint object map",
    "bounded homotopy localized right-adjoint morphism map",
    "bounded homotopy localized right-adjoint identity law",
    "bounded homotopy localized right-adjoint composition law"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1492.length =
      4 :=
  rfl

/-- W1492 replaces one right-adjoint functor package by four functor fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsRightAdjointInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1492_count]
  decide

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1492 :
    List String :=
  ["target-difference surjectivity primitive family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1492.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1492 :
    List String :=
  ["target-difference surjectivity preimage chooser family",
    "target-difference surjectivity preimage equation family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one target-surjectivity primitive family by witness fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsTargetSurjectivityInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1492_count]
  decide

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1492 :
    List String :=
  ["target-codomain compact no-univ membership primitive family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1492.length =
      1 :=
  rfl

def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1492 :
    List String :=
  ["target-codomain compact no-univ membership point chooser family",
    "target-codomain compact no-univ membership neighbourhood-meet equation family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one target compactness primitive family by witness fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsTargetCompactnessInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1492_count]
  decide

/-- W1492 records the bundled mapped explicit cokernel closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1492 :
    List String :=
  ["mapped explicit cokernel closed-embedding raw field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component mapped explicit cokernel input fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1492 :
    List String :=
  ["mapped explicit cokernel embedding raw field",
    "mapped explicit cokernel closed-range raw field"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one mapped explicit cokernel closed-embedding field by two component fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsMappedCokernelInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1492_count]
  decide

/-- W1492 records the bundled endpoint closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1492 :
    List String :=
  ["endpoint closed-embedding family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component endpoint closed-embedding input fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1492 :
    List String :=
  ["endpoint incoming-map embedding family",
    "endpoint incoming-map closed-range family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one endpoint closed-embedding family by two component fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsEndpointClosedEmbeddingInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1492_count]
  decide

/-- W1492 records the bundled endpoint open-map input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointOpenMapInputNamesW1492 :
    List String :=
  ["endpoint open-map family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointOpenMapInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointOpenMapInputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the unfolded endpoint open-map input field. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointOpenMapInputNamesW1492 :
    List String :=
  ["endpoint open-map image-openness family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointOpenMapInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointOpenMapInputNamesW1492.length =
      1 :=
  rfl

/-- W1492 unfolds the endpoint open-map input to its image-openness field. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionUnfoldsEndpointOpenMapInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointOpenMapInputNamesW1492.length =
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointOpenMapInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointOpenMapInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointOpenMapInputNamesW1492_count]

/-- W1492 records the bundled endpoint cokernel-top input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointCokernelTopInputNamesW1492 :
    List String :=
  ["endpoint cokernel-top family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointCokernelTopInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointCokernelTopInputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component endpoint cokernel-top witness fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointCokernelTopInputNamesW1492 :
    List String :=
  ["endpoint cokernel preimage chooser family",
    "endpoint cokernel preimage equation family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointCokernelTopInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointCokernelTopInputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one endpoint cokernel-top family by two witness fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsEndpointCokernelTopInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointCokernelTopInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointCokernelTopInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointCokernelTopInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointCokernelTopInputNamesW1492_count]
  decide

/-- W1492 records the bundled endpoint kernel-equality input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointKernelEqualityInputNamesW1492 :
    List String :=
  ["endpoint kernel-equality family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointKernelEqualityInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointKernelEqualityInputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component endpoint kernel-equality input fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointKernelEqualityInputNamesW1492 :
    List String :=
  ["endpoint kernel forward implication family",
    "endpoint kernel backward implication family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointKernelEqualityInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointKernelEqualityInputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one endpoint kernel-equality family by two implication fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsEndpointKernelEqualityInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointKernelEqualityInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointKernelEqualityInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointKernelEqualityInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointKernelEqualityInputNamesW1492_count]
  decide

/-- W1492 records the bundled unit mapping-cone closed-embedding input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1492 :
    List String :=
  ["unit mapping-cone closed-embedding family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component unit mapping-cone closed-embedding input fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1492 :
    List String :=
  ["unit mapping-cone incoming-map embedding family",
    "unit mapping-cone incoming-map closed-range family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one unit mapping-cone closed-embedding family by two component fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeClosedEmbeddingInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1492_count]
  decide

/-- W1492 records the bundled unit mapping-cone cokernel-top input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1492 :
    List String :=
  ["unit mapping-cone cokernel-top family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component unit mapping-cone cokernel-top witness fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1492 :
    List String :=
  ["unit mapping-cone cokernel preimage chooser family",
    "unit mapping-cone cokernel preimage equation family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one unit mapping-cone cokernel-top family by two witness fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeCokernelTopInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1492_count]
  decide

/-- W1492 records the bundled unit mapping-cone kernel-equality input. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1492 :
    List String :=
  ["unit mapping-cone kernel-equality family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1492.length =
      1 :=
  rfl

/-- W1492 records the component unit mapping-cone kernel-equality input fields. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1492 :
    List String :=
  ["unit mapping-cone kernel forward implication family",
    "unit mapping-cone kernel backward implication family"]

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1492_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1492.length =
      2 :=
  rfl

/-- W1492 replaces one unit mapping-cone kernel-equality family by two implication fields. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeKernelEqualityInput :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1492.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1492_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1492_count]
  decide

/-- W1492 preserves the W1491 input count while unfolding the endpoint open-map family. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionPreservesW1491InputCount :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1491.length =
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1491_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492_count]

/-- W1492 keeps the W1490-expanded ledger after unfolding the endpoint open-map family. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionExpandsW1490InputCount :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1490.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1490_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492_count]
  decide

/-- W1492 expands the W1477 input count after splitting the endpoint kernel equality. -/
theorem w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionExpandsW1477InputCount :
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477.length <
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492.length := by
  rw [
    w987BoundaryRelationTargetStrictPreimageMapImageFieldDataConstructionInputNamesW1477_count,
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492_count]
  decide

/-- Current W1492 nonterminal strict-preimage object-image right-adjoint functor target-compactness construction state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionStateW1492 :
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
  endpointOpenMapInputNames : List String
  componentEndpointOpenMapInputNames : List String
  endpointCokernelTopInputNames : List String
  componentEndpointCokernelTopInputNames : List String
  endpointKernelEqualityInputNames : List String
  componentEndpointKernelEqualityInputNames : List String
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

/-- W1492 records the strict-preimage object-image right-adjoint functor target-compactness construction path. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionStateW1492 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionStateW1492 where
  seed :=
    "w1492-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-endpoint-open-map-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputW1492",
      "normalizedLiftObjDataOfFieldsW1492",
      "normalizedLiftMapDataOfFieldsW1492",
      "normalizedLiftObjImageOfFieldsW1492",
      "localizedRightAdjointFunctorFieldsOfRawW1492",
      "localizedRightAdjointOfRawW1492",
      "targetDifferenceSurjectivePrimitiveOfWitnessW1492",
      "targetCodomainCompactNoUnivMembershipPrimitiveOfWitnessW1492",
      "mappedExplicitCokernelClosedEmbeddingOfFieldsW1492",
      "endpointClosedEmbeddingOfFieldsW1492",
      "endpointOpenMapOfImageOpenW1492",
      "endpointCokernelTopOfWitnessW1492",
      "endpointKernelEqualityOfFieldsW1492",
      "unitMappingConeClosedEmbeddingOfFieldsW1492",
      "unitMappingConeCokernelTopOfWitnessW1492",
      "unitMappingConeKernelEqualityOfFieldsW1492",
      "globalClosedEmbeddingComponentsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "normalizedLiftObjDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "normalizedLiftMapDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "normalizedLiftMapIdOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "normalizedLiftMapCompOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "normalizedLiftObjImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "normalizedLiftMapImageOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "normalizedLiftRawBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "normalizedLiftBlueprintOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "boundedHomotopyLocalizedRightAdjointFieldsOfW1492",
      "boundedHomotopyLocalizedRightAdjointOfW1492",
      "w1492LocalizedRightAdjointFieldsKeepObj",
      "w1492LocalizedRightAdjointFieldsKeepMap",
      "w1492LocalizedRightAdjointKeepsObj",
      "w1492LocalizedRightAdjointKeepsMap",
      "targetDifferenceSurjectiveForTargetProviderOfW1492",
      "targetCodomainCompactNoUnivMembershipProviderOfW1492",
      "w1492TargetDifferenceSurjectiveWitnessSpec",
      "w1492TargetCodomainCompactWitnessSpec",
      "w1477InputOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "localizedUnitDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
            "fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataW1492",
            "selectedDifferenceClosedEmbeddingPi1DiagramFieldOfFieldsW1492",
            "selectedDifferenceClosedEmbeddingPi2DiagramFieldOfFieldsW1492",
            "selectedDifferenceClosedEmbeddingPi3DiagramFieldOfFieldsW1492",
            "w1492SelectedDifferenceClosedEmbeddingPi1KeepsEmbedding",
            "w1492SelectedDifferenceClosedEmbeddingPi1KeepsClosedRange",
            "w1492SelectedDifferenceClosedEmbeddingPi2KeepsEmbedding",
            "w1492SelectedDifferenceClosedEmbeddingPi2KeepsClosedRange",
            "w1492SelectedDifferenceClosedEmbeddingPi3KeepsEmbedding",
            "w1492SelectedDifferenceClosedEmbeddingPi3KeepsClosedRange",
            "w1492GlobalClosedEmbeddingComponentsKeepsConstructedPi1",
            "w1492GlobalClosedEmbeddingComponentsKeepsConstructedPi2",
            "w1492GlobalClosedEmbeddingComponentsKeepsConstructedPi3",
      "w1492ClosedEmbeddingClosednessDataKeepsConstructedGlobalClosedEmbeddingComponents",
      "w1492ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1492MappedExplicitCokernelClosedEmbeddingKeepsEmbedding",
      "w1492MappedExplicitCokernelClosedEmbeddingKeepsClosedRange",
      "w1492MappedCokernelClosedEmbeddingProviderKeepsConstructedField",
      "w1492EndpointClosedEmbeddingKeepsEmbedding",
      "w1492EndpointClosedEmbeddingKeepsClosedRange",
      "w1492EndpointOpenMapKeepsImageOpen",
      "w1492EndpointCokernelTopWitnessSurjective",
      "w1492EndpointCokernelTopWitnessSpec",
      "w1492EndpointKernelEqualityKeepsForward",
      "w1492EndpointKernelEqualityKeepsBackward",
      "w1492UnitMappingConeClosedEmbeddingKeepsEmbedding",
      "w1492UnitMappingConeClosedEmbeddingKeepsClosedRange",
      "w1492UnitMappingConeCokernelTopWitnessSurjective",
      "w1492UnitMappingConeCokernelTopWitnessSpec",
      "w1492UnitMappingConeKernelEqualityKeepsForward",
      "w1492UnitMappingConeKernelEqualityKeepsBackward",
      "w1492NormalizedLiftObjDataKeepsZeroSrc",
      "w1492NormalizedLiftObjDataKeepsOneSrc",
      "w1492NormalizedLiftObjDataKeepsZeroIso",
      "w1492NormalizedLiftObjDataKeepsOneIso",
      "w1492NormalizedLiftObjDataKeepsLeftSrc",
      "w1492NormalizedLiftObjDataKeepsRightSrc",
      "w1492NormalizedLiftObjDataKeepsLeftFac",
      "w1492NormalizedLiftObjDataKeepsRightFac",
      "w1492NormalizedLiftMapDataKeepsZeroMap",
      "w1492NormalizedLiftMapDataKeepsOneMap",
      "w1492NormalizedLiftMapDataKeepsZeroMapFac",
      "w1492NormalizedLiftMapDataKeepsOneMapFac",
      "w1492NormalizedLiftMapDataKeepsLeftNaturality",
      "w1492NormalizedLiftMapDataKeepsRightNaturality",
      "w1492NormalizedLiftRawBlueprintKeepsConstructedObjData",
      "w1492NormalizedLiftRawBlueprintKeepsConstructedMapData",
      "w1492NormalizedLiftRawBlueprintKeepsMapId",
      "w1492NormalizedLiftRawBlueprintKeepsMapComp",
      "w1492NormalizedLiftBlueprintKeepsConstructedRawBlueprint",
      "w1492NormalizedLiftBlueprintKeepsObjImage",
      "w1492NormalizedLiftBlueprintKeepsMapImage",
            "w1492NormalizedLiftMapImageKeepsZeroComponent",
            "w1492NormalizedLiftMapImageKeepsOneComponent",
            "w1492W1477InputKeepsConstructedGlobalClosedEmbeddingPi1",
            "w1492W1477InputKeepsConstructedGlobalClosedEmbeddingPi2",
            "w1492W1477InputKeepsConstructedGlobalClosedEmbeddingPi3",
      "w1492W1477InputKeepsMappedCokernelClosedEmbeddingProvider",
      "w1492W1477InputKeepsConstructedEndpointClosedEmbedding",
      "w1492W1477InputKeepsConstructedEndpointOpenMap",
      "w1492W1477InputKeepsConstructedEndpointCokernelTop",
      "w1492W1477InputKeepsConstructedEndpointKernelEquality",
      "w1492W1477InputKeepsConstructedUnitMappingConeClosedEmbedding",
      "w1492W1477InputKeepsConstructedUnitMappingConeCokernelTop",
      "w1492W1477InputKeepsConstructedUnitMappingConeKernelEquality",
      "w1492W1477InputKeepsZeroSrc",
      "w1492W1477InputKeepsOneSrc",
      "w1492W1477InputKeepsZeroIso",
      "w1492W1477InputKeepsOneIso",
      "w1492W1477InputKeepsLeftSrc",
      "w1492W1477InputKeepsRightSrc",
      "w1492W1477InputKeepsLeftFac",
      "w1492W1477InputKeepsRightFac",
      "w1492W1477InputKeepsZeroMap",
      "w1492W1477InputKeepsOneMap",
      "w1492W1477InputKeepsZeroMapFac",
      "w1492W1477InputKeepsOneMapFac",
      "w1492W1477InputKeepsLeftNaturality",
      "w1492W1477InputKeepsRightNaturality",
      "w1492W1477InputKeepsZeroMapId",
      "w1492W1477InputKeepsOneMapId",
      "w1492W1477InputKeepsZeroMapComp",
      "w1492W1477InputKeepsOneMapComp",
      "w1492W1477InputKeepsNormalizedLiftObjImage",
      "w1492W1477InputKeepsNormalizedLiftZeroMapImage",
      "w1492W1477InputKeepsNormalizedLiftOneMapImage",
      "w1492W1477InputKeepsTargetDifferenceSurjective",
      "w1492W1477InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1492W1477InputKeepsConstructedLocalizedRightAdjoint",
      "w1492LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1492TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1492FullDataKeepsConstructedBoundaryRelation",
      "w1492FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi1Input",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi2Input",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsSelectedDifferencePi3Input",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1492_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1492_count",
      "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsObjectImageInput",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledRightAdjointInputNamesW1492_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentRightAdjointInputNamesW1492_count",
      "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsRightAdjointInput",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1492_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1492_count",
      "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsTargetSurjectivityInput",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1492_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1492_count",
      "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsTargetCompactnessInput",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1492_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsMappedCokernelInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsEndpointClosedEmbeddingInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointOpenMapInputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointOpenMapInputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionUnfoldsEndpointOpenMapInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointCokernelTopInputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointCokernelTopInputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsEndpointCokernelTopInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointKernelEqualityInputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointKernelEqualityInputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsEndpointKernelEqualityInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeClosedEmbeddingInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeCokernelTopInput",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1492_count",
            "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1492_count",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionSplitsUnitMappingConeKernelEqualityInput",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionPreservesW1491InputCount",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionExpandsW1490InputCount",
            "w1492BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionExpandsW1477InputCount"]
  constructionResult :=
    "proved: W1492 reconstructs the normalized lift object-image law and\
      the localized right-adjoint functor fields, reconstructs target-difference\
      surjectivity from a preimage chooser and equation, reconstructs target\
      compactness from a nonbottom filter point chooser and equation,\
      reconstructs mapped explicit cokernel closed embeddings from embedding\
      and closed-range fields, reconstructs the first, second, and third\
      selected-difference closed-embedding components from embedding and\
      closed-range fields, reconstructs endpoint closed embeddings from\
      endpoint embedding and closed-range fields, reconstructs the endpoint\
      open-map family from its unfolded image-openness field, reconstructs\
      the endpoint cokernel-top family from preimage chooser and equation\
      fields, reconstructs unit\
      mapping-cone closed embeddings from unit mapping-cone embedding and\
      closed-range fields, reconstructs the unit mapping-cone cokernel-top\
      family from preimage chooser and equation fields, reconstructs the unit\
      mapping-cone kernel equality from forward and backward implication\
      fields, reconstructs the endpoint kernel equality from forward and\
      backward implication\
      fields, then feeds those laws into W1477"
  projectionResult :=
    "proved: W1492's derived object-image law is used by the normalized lift\
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
      fields reconstruct the W1477 endpoint closed-embedding family; the\
      endpoint image-openness field reconstructs the W1477 endpoint open-map\
      family; the endpoint preimage chooser and equation fields reconstruct\
      the W1477 endpoint cokernel-top family; the endpoint forward and backward\
      implication fields reconstruct the W1477 endpoint kernel-equality\
      family; the unit\
      mapping-cone embedding and closed-range fields reconstruct the W1477\
      unit mapping-cone closed-embedding family; the unit mapping-cone\
      preimage chooser and equation fields reconstruct the W1477 cokernel-top\
      family; the unit mapping-cone forward and backward implication fields\
      reconstruct the W1477 kernel equality family; W1477 preserves the\
      map-image, raw lift blueprint, localized-unit, boundary, and\
      target/endpoint projections; product success is still not claimed"
  objectImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledObjectImageInputNamesW1492
  componentObjectImageInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentObjectImageInputNamesW1492
  targetSurjectivityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetSurjectivityInputNamesW1492
  componentTargetSurjectivityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetSurjectivityInputNamesW1492
  targetCompactnessInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledTargetCompactnessInputNamesW1492
  componentTargetCompactnessInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentTargetCompactnessInputNamesW1492
  mappedCokernelInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledMappedCokernelInputNamesW1492
  componentMappedCokernelInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentMappedCokernelInputNamesW1492
  endpointClosedEmbeddingInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointClosedEmbeddingInputNamesW1492
  componentEndpointClosedEmbeddingInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointClosedEmbeddingInputNamesW1492
  endpointOpenMapInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointOpenMapInputNamesW1492
  componentEndpointOpenMapInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointOpenMapInputNamesW1492
  endpointCokernelTopInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointCokernelTopInputNamesW1492
  componentEndpointCokernelTopInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointCokernelTopInputNamesW1492
  endpointKernelEqualityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledEndpointKernelEqualityInputNamesW1492
  componentEndpointKernelEqualityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentEndpointKernelEqualityInputNamesW1492
  unitMappingConeClosedEmbeddingInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeClosedEmbeddingInputNamesW1492
  componentUnitMappingConeClosedEmbeddingInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeClosedEmbeddingInputNamesW1492
  unitMappingConeCokernelTopInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeCokernelTopInputNamesW1492
  componentUnitMappingConeCokernelTopInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeCokernelTopInputNamesW1492
  unitMappingConeKernelEqualityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledUnitMappingConeKernelEqualityInputNamesW1492
  componentUnitMappingConeKernelEqualityInputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentUnitMappingConeKernelEqualityInputNamesW1492
  selectedDifferencePi1InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi1InputNamesW1492
  componentSelectedDifferencePi1InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi1InputNamesW1492
  selectedDifferencePi2InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi2InputNamesW1492
  componentSelectedDifferencePi2InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi2InputNamesW1492
  selectedDifferencePi3InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionBundledSelectedDifferencePi3InputNamesW1492
  componentSelectedDifferencePi3InputNames :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionComponentSelectedDifferencePi3InputNamesW1492
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionInputNamesW1492
  productSuccessClaimed := false

theorem currentW1492W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3FieldDataConstructionStateW1492.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
