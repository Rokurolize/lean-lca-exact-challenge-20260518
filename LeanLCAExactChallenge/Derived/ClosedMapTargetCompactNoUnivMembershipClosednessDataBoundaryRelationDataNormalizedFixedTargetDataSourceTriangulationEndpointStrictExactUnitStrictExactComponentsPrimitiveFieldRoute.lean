import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute

/-!
W943 feeds the W942 closed-map target-compact closedness-data boundary-relation
route while replacing the normalized strict-representative lift blueprint and
the two fixed-target uniqueness fields by the existing W719 normalized
fixed-target data provider.
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

/--
W943 preserves W942's boundary, relation, target, closedness,
source-triangulation, endpoint strict-exact, and localized unit fields, while
bundling the normalized lift blueprint and both fixed-target uniqueness
obligations through W719.
-/
structure MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW943 :
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
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
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
W943 projects W942 leaves by unpacking W719 normalized fixed-target data.
-/
def w942LeavesOfNormalizedFixedTargetDataClosednessDataBoundaryRelationDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW943) :
    MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW942
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactSpaceProvider :=
    leaves.targetCodomainCompactSpaceProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedStrictRepresentativeLiftBlueprint :=
    normalizedLiftBlueprint_of_normalizedFixedTargetDataW719
      leaves.normalizedFixedTargetData
  targetFixedTargetUniq :=
    targetFixedTargetUniq_of_normalizedFixedTargetDataW719
      leaves.normalizedFixedTargetData
  localizationModelFixedTargetUniq :=
    localizationModelFixedTargetUniq_of_normalizedFixedTargetDataW719
      leaves.normalizedFixedTargetData
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointStrictExact := leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    leaves.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W943 W733 concrete leaves after projecting W942 leaves. -/
def concreteLeavesOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW943) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
    (w942LeavesOfNormalizedFixedTargetDataClosednessDataBoundaryRelationDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
      leaves)

/-- W943 W732 route data after projecting W942 leaves. -/
def routeDataProviderOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW943) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
    (w942LeavesOfNormalizedFixedTargetDataClosednessDataBoundaryRelationDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW943) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
    (w942LeavesOfNormalizedFixedTargetDataClosednessDataBoundaryRelationDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
    (leaves :
      MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW943) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW942
    (w942LeavesOfNormalizedFixedTargetDataClosednessDataBoundaryRelationDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
      leaves)

/--
W943 exposes W942's route with the normalized lift blueprint and two
fixed-target uniqueness obligations consolidated into one W719 provider.
-/
def closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW943 :
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
    "W719 normalized fixed-target data provider: normalized strict-representative\
      lift blueprint, target fixed-target uniqueness, and localization-model\
      fixed-target uniqueness",
    "bundled W722 source-triangulation data provider: pretriangulated,\
      triangulated, and source-side triangle-completion data",
    "endpoint strict short-exact witnesses for closed embeddings, open maps,\
      and outgoing epi data",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone iso-closure witness: degreewise strict components\
      (closed inclusion, open map, surjectivity, algebraic exactness) plus\
      isomorphism"]

theorem closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW943_count :
    closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW943.length =
      11 :=
  rfl

/-- Current checked W943 state. -/
structure MetrizableClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW943 :
    Type where
  seed : String
  declarations : List String
  normalizedFixedTargetDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW943 :
    MetrizableClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW943
    where
  seed :=
    "w943-closed-map-target-compact-no-univ-membership-closedness-data-boundary-\
      relation-data-normalized-fixed-target-data-source-triangulation-endpoint-\
      strict-exact-unit-strict-exact-components-primitive-field-route"
  declarations :=
    ["MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW943",
      "w942LeavesOfNormalizedFixedTargetDataClosednessDataBoundaryRelationDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943",
      "concreteLeavesOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943",
      "routeDataProviderOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943",
      "directBoundedLeftCalculusOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943",
      "boundedDerivedInfinityCategoryOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943",
      "closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW943",
      "closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW943_count"]
  normalizedFixedTargetDataResult :=
    "proved: W719 projects the normalized strict-representative lift blueprint,\
      target fixed-target uniqueness, and localization-model fixed-target\
      uniqueness required by W942"
  exactAtResult :=
    "proved: closed-map target-compact-no-univ-membership-closedness-data-\
      boundary-relation-data-normalized-fixed-target-data-source-triangulation-\
      endpoint-strict-exact-unit-strict-exact-components route feeds the\
      W942/W941/W940/W937/W936/W935/W934/W933/W932/W931/W930 stable ExactAt\
      route"
  refinedInputs :=
    ["normalized strict-representative lift blueprint and both fixed-target\
      uniqueness obligations replaced by W719 normalized fixed-target data",
      "selected-difference and mapped-cokernel closedness remain consolidated\
      into W725",
      "boundary and relation leaves remain consolidated into W716 and W717\
      providers",
      "source triangulation remains consolidated into W722",
      "endpoint closed-embedding, open-map, and ShortExact leaves remain\
      consolidated into one endpoint strict MetrizableLCA short exact witness"]
  remainingInputs :=
    closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW943
  productSuccessClaimed := false

theorem currentW943ClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW943;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
