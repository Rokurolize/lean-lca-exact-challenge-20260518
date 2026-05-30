import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute

/-!
W941 feeds the W940 closed-map target-compact normalized strict-representative
lift source-triangulation endpoint-strict-exact unit-strict-exact-components
route while replacing the raw WPP boundary and closed-natural-transformation
relation fields by the existing W716 and W717 bundled providers.
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
W941 preserves W940's target, selected-difference, mapped-cokernel,
normalized-lift, source-triangulation, endpoint strict-exact, and localized
unit fields, while bundling the two boundary fields through W716 and the two
relation fields through W717.
-/
structure MetrizableWppClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW941 :
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
  closedMapPi1 :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi1PrimitiveW922 S
  closedMapPi2 :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi2PrimitiveW922 S
  closedMapPi3 :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi3PrimitiveW922 S
  mappedCokernelClosedMap :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      mappedCokernelClosedMapPrimitiveW921 f
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
W941 projects W940 leaves by unpacking W716 boundary data and W717 relation
data through their existing accessors.
-/
def w940LeavesOfBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
    (leaves :
      MetrizableWppClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW941) :
    MetrizableWppClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW940
    where
  rightOpenBoundary :=
    rightOpenBoundary_of_boundaryDataW716 leaves.boundaryData
  sourcePiZeroBoundary :=
    sourcePiZeroBoundary_of_boundaryDataW716 leaves.boundaryData
  relationPullbackProvider :=
    relationPullbackProvider_of_relationDataW717 leaves.relationData
  targetRelationLiftsProvider :=
    targetRelationLiftsProvider_of_relationDataW717 leaves.relationData
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactSpaceProvider :=
    leaves.targetCodomainCompactSpaceProvider
  closedMapPi1 := leaves.closedMapPi1
  closedMapPi2 := leaves.closedMapPi2
  closedMapPi3 := leaves.closedMapPi3
  mappedCokernelClosedMap := leaves.mappedCokernelClosedMap
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

/-- W941 W733 concrete leaves after projecting W940 leaves. -/
def concreteLeavesOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
    (leaves :
      MetrizableWppClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW941) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
    (w940LeavesOfBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
      leaves)

/-- W941 W732 route data after projecting W940 leaves. -/
def routeDataProviderOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
    (leaves :
      MetrizableWppClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW941) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
    (w940LeavesOfBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
    (leaves :
      MetrizableWppClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW941) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
    (w940LeavesOfBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
    (leaves :
      MetrizableWppClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW941) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetCompactNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW940
    (w940LeavesOfBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941
      leaves)

/--
W941 exposes boundary and relation assumptions as existing semantic providers
while retaining W940's normalized lift, source, endpoint, and unit fields.
-/
def closedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW941 :
    List String :=
  ["bundled W716 WPP-limit boundary data provider: right-open closed-quotient-cover\
      boundary and source-difference cokernel-pi-zero boundary",
    "bundled W717 closed-natural-transformation relation data provider: relation\
      pullback and target-relation lifting",
    "primitive target-difference preimage quantifier for every target diagram",
    "primitive target-codomain compactness filter nonbottom and point meet nonbottom\
      for every target diagram",
    "primitive selected-difference pi1 closed-set image condition",
    "primitive selected-difference pi2 closed-set image condition",
    "primitive selected-difference pi3 closed-set image condition",
    "primitive mapped explicit cokernel closed-set image condition for every morphism",
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

theorem closedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW941_count :
    closedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW941.length =
      16 :=
  rfl

/-- Current checked W941 state. -/
structure MetrizableClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW941 :
    Type where
  seed : String
  declarations : List String
  boundaryRelationResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW941 :
    MetrizableClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW941
    where
  seed :=
    "w941-closed-map-target-compact-no-univ-membership-boundary-relation-data-\
      normalized-strict-representative-lift-source-triangulation-endpoint-\
      strict-exact-unit-strict-exact-components-primitive-field-route"
  declarations :=
    ["MetrizableWppClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW941",
      "w940LeavesOfBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941",
      "concreteLeavesOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941",
      "routeDataProviderOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941",
      "directBoundedLeftCalculusOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941",
      "boundedDerivedInfinityCategoryOfClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW941",
      "closedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW941",
      "closedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW941_count"]
  boundaryRelationResult :=
    "proved: W716 boundary data supplies W940's right-open and source-pi-zero\
      boundary leaves, and W717 relation data supplies W940's relation-pullback\
      and target-relation-lift leaves"
  exactAtResult :=
    "proved: closed-map target-compact-no-univ-membership-boundary-relation-data-\
      normalized-strict-representative-lift-source-triangulation-data-endpoint-\
      strict-exact-unit-strict-exact-components route feeds the W940/W937/W936/\
      W935/W934/W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["raw right-open and source-pi-zero WPP boundary leaves replaced by the\
      existing W716 boundary-data provider",
      "raw relation-pullback and target-relation-lift leaves replaced by the\
      existing W717 relation-data provider",
      "strict preimage object/map/coherence/source-image leaves remain\
      consolidated into the normalized strict-representative lift blueprint",
      "raw source Pretriangulated, IsTriangulated, and triangle-completion\
      leaves remain consolidated into the W722 source-triangulation data\
      provider",
      "endpoint closed-embedding, open-map, and ShortExact leaves remain\
      consolidated into one endpoint strict MetrizableLCA short exact witness"]
  remainingInputs :=
    closedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW941
  productSuccessClaimed := false

theorem currentW941ClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapTargetCompactBoundaryRelationDataNormalizedStrictRepresentativeLiftSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW941;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
