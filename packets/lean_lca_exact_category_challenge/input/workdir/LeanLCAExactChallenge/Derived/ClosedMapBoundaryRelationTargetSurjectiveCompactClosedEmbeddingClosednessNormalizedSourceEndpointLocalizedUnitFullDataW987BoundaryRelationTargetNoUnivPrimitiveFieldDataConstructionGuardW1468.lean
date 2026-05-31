import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionGuardW1467

/-!
W1468 refines W1467 by constructing the W944 target no-univ provider from the
two target primitive families, then running the resulting data through the
W1467 W987 construction.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace Dbounded

noncomputable section

/--
W1468 replaces W1467's W944 target no-univ provider by the two target primitive
families used to construct that provider.
-/
structure W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468 :
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
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  normalizedLiftBlueprint :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
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

/-- W1468 builds W944 target no-univ data from the two target primitive families. -/
def targetNoUnivDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  fun Y =>
    ⟨input.targetDifferenceSurjectiveForTargetProvider Y,
      input.targetCodomainCompactNoUnivMembershipProvider Y⟩

/-- W1468 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1468
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1468 builds the W1467 input after reconstructing W944 target no-univ data. -/
def w1467InputOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    W987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputW1467 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetNoUnivData :=
    targetNoUnivDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
      input
  closedEmbeddingClosednessData := input.closedEmbeddingClosednessData
  normalizedLiftBlueprint := input.normalizedLiftBlueprint
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

/-- W1468 builds W945 localized-unit data through W1467. -/
def localizedUnitDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (w1467InputOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
      input)

/-- W1468 builds W730 boundary/relation data through W1467. -/
def boundaryRelationDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (w1467InputOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
      input)

/-- W1468 builds W986 target/endpoint data through W1467. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (w1467InputOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
      input)

/-- W1468 builds W987 full data through W1467. -/
noncomputable def fullDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataW1467
    (w1467InputOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
      input)

/-- W1468's constructed W944 data keeps target-difference surjectivity. -/
theorem w1468TargetNoUnivDataKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    targetDifferenceSurjectivePrimitiveOfTargetNoUnivDataW944
        (targetNoUnivDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
          input) =
      input.targetDifferenceSurjectiveForTargetProvider := by
  funext Y
  rfl

/-- W1468's constructed W944 data keeps target-codomain compact no-univ membership. -/
theorem w1468TargetNoUnivDataKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    targetCodomainCompactNoUnivMembershipPrimitiveOfTargetNoUnivDataW944
        (targetNoUnivDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
          input) =
      input.targetCodomainCompactNoUnivMembershipProvider := by
  funext Y
  rfl

/-- W1468's W1467 input keeps the constructed W944 target no-univ data. -/
theorem w1468W1467InputKeepsConstructedTargetNoUnivData
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    (w1467InputOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
        input).targetNoUnivData =
      targetNoUnivDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
        input :=
  rfl

/-- W1468's W1467 input keeps W973 closed-embedding closedness data. -/
theorem w1468W1467InputKeepsClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    (w1467InputOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
        input).closedEmbeddingClosednessData =
      input.closedEmbeddingClosednessData :=
  rfl

/-- W1468's W1467 input keeps the reconstructed localized right adjoint. -/
theorem w1468W1467InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    boundedHomotopyLocalizedRightAdjointOfW1467
        (w1467InputOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1468 input :=
  rfl

/-- W1468's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1468LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1468 input :=
  rfl

/-- W1468's W986 construction keeps the constructed W944 target no-univ data. -/
theorem w1468TargetNormalizedEndpointKeepsConstructedTargetNoUnivData
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    targetNoUnivDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
            input)) =
      targetNoUnivDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
        input :=
  rfl

/-- W1468's constructed W987 provider projects to the constructed W730 data. -/
theorem w1468FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
        input :=
  rfl

/-- W1468's constructed W987 provider projects to the constructed W986 data. -/
theorem w1468FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
        input :=
  rfl

def w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputNamesW1468 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "target-difference surjectivity primitive family",
    "target-codomain compact no-univ membership primitive family",
    "W973 closed-embedding closedness data",
    "normalized lift blueprint",
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

theorem w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputNamesW1468_count :
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputNamesW1468.length =
      36 :=
  rfl

def w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionBundledTargetInputNamesW1468 :
    List String :=
  ["W944 target no-univ data"]

theorem w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionBundledTargetInputNamesW1468_count :
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionBundledTargetInputNamesW1468.length =
      1 :=
  rfl

def w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionPrimitiveTargetInputNamesW1468 :
    List String :=
  ["target-difference surjectivity primitive family",
    "target-codomain compact no-univ membership primitive family"]

theorem w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionPrimitiveTargetInputNamesW1468_count :
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionPrimitiveTargetInputNamesW1468.length =
      2 :=
  rfl

/-- W1468 replaces one W944 target no-univ provider by two primitive target inputs. -/
theorem w1468BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionSplitsW944Input :
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionBundledTargetInputNamesW1468.length <
      w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionPrimitiveTargetInputNamesW1468.length := by
  rw [
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionBundledTargetInputNamesW1468_count,
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionPrimitiveTargetInputNamesW1468_count]
  decide

/-- W1468 expands the W1467 input count by decomposing W944 target no-univ data. -/
theorem w1468BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionExpandsW1467InputCount :
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputNamesW1467.length <
      w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputNamesW1468.length := by
  rw [
    w987BoundaryRelationTargetLocalizedRightAdjointFunctorFieldDataConstructionInputNamesW1467_count,
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputNamesW1468_count]
  decide

/-- Current W1468 nonterminal target primitive construction state. -/
structure W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionStateW1468 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  targetPrimitiveInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1468 records the target primitive construction path. -/
def currentW987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionStateW1468 :
    W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionStateW1468 where
  seed :=
    "w1468-w987-boundary-relation-target-no-univ-primitive-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468",
      "targetNoUnivDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468",
      "boundedHomotopyLocalizedRightAdjointOfW1468",
      "w1467InputOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468",
      "localizedUnitDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468",
      "boundaryRelationDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468",
      "fullDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468",
      "w1468TargetNoUnivDataKeepsTargetDifferenceSurjective",
      "w1468TargetNoUnivDataKeepsTargetCodomainCompactNoUnivMembership",
      "w1468W1467InputKeepsConstructedTargetNoUnivData",
      "w1468W1467InputKeepsClosedEmbeddingClosednessData",
      "w1468W1467InputKeepsConstructedLocalizedRightAdjoint",
      "w1468LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1468TargetNormalizedEndpointKeepsConstructedTargetNoUnivData",
      "w1468FullDataKeepsConstructedBoundaryRelation",
      "w1468FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputNamesW1468_count",
      "w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionBundledTargetInputNamesW1468_count",
      "w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionPrimitiveTargetInputNamesW1468_count",
      "w1468BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionSplitsW944Input",
      "w1468BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionExpandsW1467InputCount"]
  constructionResult :=
    "proved: W1468 reconstructs W944 target no-univ data from the\
      target-difference surjectivity and target-codomain compact no-univ\
      membership primitive families, then feeds that provider into W1467"
  projectionResult :=
    "proved: the constructed W944 provider projects back to the two primitive\
      target families while W1467 preserves localized-unit, boundary, and\
      target/endpoint projections; product success is still not claimed"
  targetPrimitiveInputNames :=
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionPrimitiveTargetInputNamesW1468
  remainingInputs :=
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputNamesW1468
  productSuccessClaimed := false

theorem currentW1468W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionStateW1468.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
