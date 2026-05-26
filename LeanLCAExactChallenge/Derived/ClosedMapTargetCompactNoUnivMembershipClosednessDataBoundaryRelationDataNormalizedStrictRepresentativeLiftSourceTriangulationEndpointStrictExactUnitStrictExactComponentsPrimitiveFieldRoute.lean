import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute

/-!
W942 feeds the W941 closed-map target-compact boundary-relation-data normalized
strict-representative lift source-triangulation endpoint-strict-exact
unit-strict-exact-components route while replacing the selected-difference and
mapped-cokernel closedness primitive fields by the existing W725 closedness
branch data.
-/

set_option autoImplicit false

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

namespace Dbounded

/-- W942 projects the primitive selected-difference π₁ closed-map leaf from W725 data. -/
@[reducible]
def selectedDifferenceClosedMapPi1PrimitiveOfClosednessDataW942
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi1PrimitiveW922 S := by
  intro S
  cases closednessData with
  | closedMap globalClosedMapComponents _mappedCokernelClosedMapProvider =>
      simpa [selectedDifferenceClosedMapPi1PrimitiveW922, IsClosedMap]
        using
          (selectedDifferenceClosedMapPi1DiagramField_of_componentProviderW718
            globalClosedMapComponents S)
  | closedEmbedding globalClosedEmbeddingComponents _mappedCokernelClosedEmbeddingProvider =>
      simpa [selectedDifferenceClosedMapPi1PrimitiveW922, IsClosedMap]
        using
          ((selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
            globalClosedEmbeddingComponents S).isClosedMap)

/-- W942 projects the primitive selected-difference π₂ closed-map leaf from W725 data. -/
@[reducible]
def selectedDifferenceClosedMapPi2PrimitiveOfClosednessDataW942
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi2PrimitiveW922 S := by
  intro S
  cases closednessData with
  | closedMap globalClosedMapComponents _mappedCokernelClosedMapProvider =>
      simpa [selectedDifferenceClosedMapPi2PrimitiveW922, IsClosedMap]
        using
          (selectedDifferenceClosedMapPi2DiagramField_of_componentProviderW718
            globalClosedMapComponents S)
  | closedEmbedding globalClosedEmbeddingComponents _mappedCokernelClosedEmbeddingProvider =>
      simpa [selectedDifferenceClosedMapPi2PrimitiveW922, IsClosedMap]
        using
          ((selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
            globalClosedEmbeddingComponents S).isClosedMap)

/-- W942 projects the primitive selected-difference π₃ closed-map leaf from W725 data. -/
@[reducible]
def selectedDifferenceClosedMapPi3PrimitiveOfClosednessDataW942
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi3PrimitiveW922 S := by
  intro S
  cases closednessData with
  | closedMap globalClosedMapComponents _mappedCokernelClosedMapProvider =>
      simpa [selectedDifferenceClosedMapPi3PrimitiveW922, IsClosedMap]
        using
          (selectedDifferenceClosedMapPi3DiagramField_of_componentProviderW718
            globalClosedMapComponents S)
  | closedEmbedding globalClosedEmbeddingComponents _mappedCokernelClosedEmbeddingProvider =>
      simpa [selectedDifferenceClosedMapPi3PrimitiveW922, IsClosedMap]
        using
          ((selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
            globalClosedEmbeddingComponents S).isClosedMap)

/-- W942 projects the primitive mapped-cokernel closed-map leaf from W725 data. -/
@[reducible]
def mappedCokernelClosedMapPrimitiveOfClosednessDataW942
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725) :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      mappedCokernelClosedMapPrimitiveW921 f := by
  intro X Y f
  cases closednessData with
  | closedMap _globalClosedMapComponents mappedCokernelClosedMapProvider =>
      simpa [mappedCokernelClosedMapPrimitiveW921, IsClosedMap]
        using (mappedCokernelClosedMapProvider.isClosedMap f)
  | closedEmbedding _globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider =>
      simpa [mappedCokernelClosedMapPrimitiveW921, IsClosedMap]
        using ((mappedCokernelClosedEmbeddingProvider.isClosedEmbedding f).isClosedMap)

/--
W942 preserves W941's boundary, relation, target, normalized-lift,
source-triangulation, endpoint strict-exact, and localized unit fields, while
bundling selected-difference and mapped-cokernel closedness through W725.
-/
structure MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW942 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetDifferenceSurjectiveForTargetProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y
  targetCodomainCompactSpaceProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  normalizedStrictRepresentativeLiftBlueprint :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
  targetFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  localizationModelFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      boundedHomotopyLocalizedRightAdjoint
      boundedHomotopyLocalizedAdjunction

/--
W942 projects W941 leaves by unpacking W725 closedness data to primitive
selected-difference and mapped-cokernel closed-map leaves.
-/
def w941LeavesOfClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW942) :
    MetrizableWppClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW941
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactSpaceProvider :=
    leaves.targetCodomainCompactSpaceProvider
  closedMapPi1 :=
    selectedDifferenceClosedMapPi1PrimitiveOfClosednessDataW942
      leaves.diagramAndMappedCokernelClosednessData
  closedMapPi2 :=
    selectedDifferenceClosedMapPi2PrimitiveOfClosednessDataW942
      leaves.diagramAndMappedCokernelClosednessData
  closedMapPi3 :=
    selectedDifferenceClosedMapPi3PrimitiveOfClosednessDataW942
      leaves.diagramAndMappedCokernelClosednessData
  mappedCokernelClosedMap :=
    mappedCokernelClosedMapPrimitiveOfClosednessDataW942
      leaves.diagramAndMappedCokernelClosednessData
  normalizedStrictRepresentativeLiftBlueprint :=
    leaves.normalizedStrictRepresentativeLiftBlueprint
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq :=
    leaves.localizationModelFixedTargetUniq
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointStrictExact := leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    leaves.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W942 W733 concrete leaves after projecting W941 leaves. -/
def concreteLeavesOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW942) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
    (w941LeavesOfClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
      leaves)

/-- W942 W732 route data after projecting W941 leaves. -/
def routeDataProviderOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW942) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
    (w941LeavesOfClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW942) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
    (w941LeavesOfClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW942) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
    (w941LeavesOfClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
      leaves)

/--
W942 exposes selected-difference and mapped-cokernel closedness as one W725
closedness branch while retaining W941's boundary, relation, target, source,
endpoint, and unit fields.
-/
def closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW942 :
    List String :=
  ["bundled W716 WPP-limit boundary data provider: right-open closed-quotient-cover\
      boundary and source-difference cokernel-pi-zero boundary",
    "bundled W717 closed-natural-transformation relation data provider: relation\
      pullback and target-relation lifting",
    "primitive target-difference preimage quantifier for every target diagram",
    "primitive target-codomain compactness filter nonbottom and point meet nonbottom\
      for every target diagram",
    "W725 selected-difference and mapped-cokernel closedness branch: closed map\
      or closed embedding data",
    "normalized strict-representative lift blueprint: object data, map data,\
      identity and composition coherence, and source-image normalization",
    "target fixed-target uniqueness quantifier for objectwise localization",
    "localization-model fixed-target uniqueness quantifier for objectwise localization",
    "bundled W722 source-triangulation data provider: pretriangulated,\
      triangulated, and source-side triangle-completion data",
    "endpoint strict short-exact witnesses for closed embeddings, open maps,\
      and outgoing epi data",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone iso-closure witness: degreewise strict components\
      (closed inclusion, open map, surjectivity, algebraic exactness) plus\
      isomorphism"]

theorem closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW942_count :
    closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW942.length =
      13 :=
  rfl

/-- Current checked W942 state. -/
structure MetrizableClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW942 :
    Type where
  seed : String
  declarations : List String
  closednessDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW942 :
    MetrizableClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW942
    where
  seed :=
    "w942-closed-map-target-compact-no-univ-membership-closedness-data-boundary-\
      relation-data-normalized-strict-representative-lift-source-triangulation-\
      endpoint-strict-exact-unit-strict-exact-components-primitive-field-route"
  declarations :=
    ["selectedDifferenceClosedMapPi1PrimitiveOfClosednessDataW942",
      "selectedDifferenceClosedMapPi2PrimitiveOfClosednessDataW942",
      "selectedDifferenceClosedMapPi3PrimitiveOfClosednessDataW942",
      "mappedCokernelClosedMapPrimitiveOfClosednessDataW942",
      "MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW942",
      "w941LeavesOfClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942",
      "concreteLeavesOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942",
      "routeDataProviderOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942",
      "directBoundedLeftCalculusOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942",
      "boundedDerivedInfinityCategoryOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942",
      "closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW942",
      "closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW942_count"]
  closednessDataResult :=
    "proved: W725 closed-map branch supplies W941's selected-difference and\
      mapped-cokernel primitive closed-map leaves directly, and W725\
      closed-embedding branch supplies them through IsClosedEmbedding.isClosedMap"
  exactAtResult :=
    "proved: closed-map target-compact-no-univ-membership-closedness-data-\
      boundary-relation-data-normalized-strict-representative-lift-source-\
      triangulation-data-endpoint-strict-exact-unit-strict-exact-components\
      route feeds the W941/W940/W937/W936/W935/W934/W933/W932/W931/W930\
      stable ExactAt route"
  refinedInputs :=
    ["primitive selected-difference pi1, pi2, and pi3 closed-set image leaves\
      replaced by the existing W725 closedness branch",
      "primitive mapped explicit cokernel closed-set image leaf replaced by\
      the existing W725 closedness branch",
      "boundary and relation leaves remain consolidated into W716 and W717\
      providers",
      "strict preimage object/map/coherence/source-image leaves remain\
      consolidated into the normalized strict-representative lift blueprint",
      "endpoint closed-embedding, open-map, and ShortExact leaves remain\
      consolidated into one endpoint strict MetrizableLCA short exact witness"]
  remainingInputs :=
    closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW942
  productSuccessClaimed := false

theorem currentW942ClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW942;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
