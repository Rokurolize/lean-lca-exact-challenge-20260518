import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionGuardW1468

/-!
W1469 refines W1468 by constructing the W973 closed-embedding closedness
provider from its W718 selected-difference closed-embedding component provider
and W519 mapped explicit cokernel closed-embedding provider, then running the
resulting data through the W1468 W987 construction.
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
W1469 replaces W1468's W973 closed-embedding closedness provider by the two
fields used to construct that provider.
-/
structure W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469 :
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
  globalClosedEmbeddingComponents :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
  mappedCokernelClosedEmbeddingProvider :
    MappedExplicitCokernelClosedEmbeddingProviderW519
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

/-- W1469 builds W973 closed-embedding closedness data from its two fields. -/
def closedEmbeddingClosednessDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents := input.globalClosedEmbeddingComponents
  mappedCokernelClosedEmbeddingProvider :=
    input.mappedCokernelClosedEmbeddingProvider

/-- W1469 names the reconstructed localized right adjoint for an input package. -/
def boundedHomotopyLocalizedRightAdjointOfW1469
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    BoundedHomotopyLocalizedCategoryW1461 ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedRightAdjointOfW1467
    input.boundedHomotopyLocalizedRightAdjointFields

/-- W1469 builds the W1468 input after reconstructing W973 closedness data. -/
def w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    W987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputW1468 where
  rightOpenBoundary := input.rightOpenBoundary
  sourcePiZeroBoundary := input.sourcePiZeroBoundary
  relationPullbackProvider := input.relationPullbackProvider
  targetRelationLiftsProvider := input.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    input.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactNoUnivMembershipProvider :=
    input.targetCodomainCompactNoUnivMembershipProvider
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
      input
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

/-- W1469 builds W945 localized-unit data through W1468. -/
def localizedUnitDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
      input)

/-- W1469 builds W730 boundary/relation data through W1468. -/
def boundaryRelationDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
      input)

/-- W1469 builds W986 target/endpoint data through W1468. -/
def targetNormalizedEndpointDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  targetNormalizedEndpointDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
      input)

/-- W1469 builds W987 full data through W1468. -/
noncomputable def fullDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetNoUnivPrimitiveFieldDataW1468
    (w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
      input)

/-- W1469's constructed W973 data keeps W718 selected-difference components. -/
theorem w1469ClosedEmbeddingClosednessDataKeepsGlobalClosedEmbeddingComponents
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
          input) =
      input.globalClosedEmbeddingComponents :=
  rfl

/-- W1469's constructed W973 data keeps W519 mapped-cokernel data. -/
theorem w1469ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        (closedEmbeddingClosednessDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
          input) =
      input.mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1469's W1468 input keeps the constructed W973 closedness data. -/
theorem w1469W1468InputKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    (w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
        input).closedEmbeddingClosednessData =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
        input :=
  rfl

/-- W1469's W1468 input keeps target-difference surjectivity. -/
theorem w1469W1468InputKeepsTargetDifferenceSurjective
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    (w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
        input).targetDifferenceSurjectiveForTargetProvider =
      input.targetDifferenceSurjectiveForTargetProvider :=
  rfl

/-- W1469's W1468 input keeps target-codomain compact no-univ membership. -/
theorem w1469W1468InputKeepsTargetCodomainCompactNoUnivMembership
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    (w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
        input).targetCodomainCompactNoUnivMembershipProvider =
      input.targetCodomainCompactNoUnivMembershipProvider :=
  rfl

/-- W1469's W1468 input keeps the reconstructed localized right adjoint. -/
theorem w1469W1468InputKeepsConstructedLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    boundedHomotopyLocalizedRightAdjointOfW1468
        (w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1469 input :=
  rfl

/-- W1469's constructed W945 data keeps the reconstructed localized right adjoint. -/
theorem w1469LocalizedUnitDataKeepsLocalizedRightAdjoint
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
          input) =
      boundedHomotopyLocalizedRightAdjointOfW1469 input :=
  rfl

/-- W1469's W986 construction keeps the constructed W973 closedness data. -/
theorem w1469TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
          (targetNormalizedEndpointDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
            input)) =
      closedEmbeddingClosednessDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
        input :=
  rfl

/-- W1469's constructed W987 provider projects to the constructed W730 data. -/
theorem w1469FullDataKeepsConstructedBoundaryRelation
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
        input :=
  rfl

/-- W1469's constructed W987 provider projects to the constructed W986 data. -/
theorem w1469FullDataKeepsConstructedTargetNormalizedEndpoint
    (input :
      W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469
        input :=
  rfl

def w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputNamesW1469 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary field",
    "raw source-difference cokernel-pi-zero WPP-limit boundary field",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "target-difference surjectivity primitive family",
    "target-codomain compact no-univ membership primitive family",
    "W718 selected-difference closed-embedding diagram component provider",
    "W519 mapped explicit cokernel closed-embedding provider",
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

theorem w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputNamesW1469_count :
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputNamesW1469.length =
      37 :=
  rfl

def w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionBundledClosednessInputNamesW1469 :
    List String :=
  ["W973 closed-embedding closedness data"]

theorem w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionBundledClosednessInputNamesW1469_count :
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionBundledClosednessInputNamesW1469.length =
      1 :=
  rfl

def w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionClosednessFieldInputNamesW1469 :
    List String :=
  ["W718 selected-difference closed-embedding diagram component provider",
    "W519 mapped explicit cokernel closed-embedding provider"]

theorem w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionClosednessFieldInputNamesW1469_count :
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionClosednessFieldInputNamesW1469.length =
      2 :=
  rfl

/-- W1469 replaces one W973 closedness provider by two closedness fields. -/
theorem w1469BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionSplitsW973Input :
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionBundledClosednessInputNamesW1469.length <
      w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionClosednessFieldInputNamesW1469.length := by
  rw [
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionBundledClosednessInputNamesW1469_count,
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionClosednessFieldInputNamesW1469_count]
  decide

/-- W1469 expands the W1468 input count by decomposing W973 closedness data. -/
theorem w1469BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionExpandsW1468InputCount :
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputNamesW1468.length <
      w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputNamesW1469.length := by
  rw [
    w987BoundaryRelationTargetNoUnivPrimitiveFieldDataConstructionInputNamesW1468_count,
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputNamesW1469_count]
  decide

/-- Current W1469 nonterminal closedness-field construction state. -/
structure W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionStateW1469 :
    Type where
  seed : String
  declarations : List String
  constructionResult : String
  projectionResult : String
  closednessFieldInputNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1469 records the W973 closedness-field construction path. -/
def currentW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionStateW1469 :
    W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionStateW1469 where
  seed :=
    "w1469-w987-boundary-relation-target-closed-embedding-closedness-field-data-construction"
  declarations :=
    ["W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputW1469",
      "closedEmbeddingClosednessDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469",
      "boundedHomotopyLocalizedRightAdjointOfW1469",
      "w1468InputOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469",
      "localizedUnitDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469",
      "boundaryRelationDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469",
      "targetNormalizedEndpointDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469",
      "fullDataOfW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataW1469",
      "w1469ClosedEmbeddingClosednessDataKeepsGlobalClosedEmbeddingComponents",
      "w1469ClosedEmbeddingClosednessDataKeepsMappedCokernelClosedEmbeddingProvider",
      "w1469W1468InputKeepsConstructedClosedEmbeddingClosednessData",
      "w1469W1468InputKeepsTargetDifferenceSurjective",
      "w1469W1468InputKeepsTargetCodomainCompactNoUnivMembership",
      "w1469W1468InputKeepsConstructedLocalizedRightAdjoint",
      "w1469LocalizedUnitDataKeepsLocalizedRightAdjoint",
      "w1469TargetNormalizedEndpointKeepsConstructedClosedEmbeddingClosednessData",
      "w1469FullDataKeepsConstructedBoundaryRelation",
      "w1469FullDataKeepsConstructedTargetNormalizedEndpoint",
      "w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputNamesW1469_count",
      "w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionBundledClosednessInputNamesW1469_count",
      "w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionClosednessFieldInputNamesW1469_count",
      "w1469BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionSplitsW973Input",
      "w1469BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionExpandsW1468InputCount"]
  constructionResult :=
    "proved: W1469 reconstructs W973 closed-embedding closedness data from the\
      W718 selected-difference closed-embedding component provider and the\
      W519 mapped explicit cokernel closed-embedding provider, then feeds that\
      provider into W1468"
  projectionResult :=
    "proved: the constructed W973 provider projects back to its two closedness\
      fields while W1468 preserves localized-unit, boundary, and\
      target/endpoint projections; product success is still not claimed"
  closednessFieldInputNames :=
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionClosednessFieldInputNamesW1469
  remainingInputs :=
    w987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionInputNamesW1469
  productSuccessClaimed := false

theorem currentW1469W987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstruction_productSuccess :
    currentW987BoundaryRelationTargetClosedEmbeddingClosednessFieldDataConstructionStateW1469.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
