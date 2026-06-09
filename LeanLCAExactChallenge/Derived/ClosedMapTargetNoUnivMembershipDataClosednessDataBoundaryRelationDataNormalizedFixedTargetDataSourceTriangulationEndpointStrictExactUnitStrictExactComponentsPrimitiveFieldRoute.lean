import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute

/-!
W944 feeds the W943 closed-map target-compact closedness-data boundary-relation
route while replacing the target-difference and target-codomain
no-univ-membership primitive fields by one target-only provider.
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
W944 target-only provider: pair the target-difference surjectivity primitive
with the W930 no-univ-membership target compactness primitive for the same
target diagram.
-/
abbrev TargetSurjectiveNoUnivMembershipForTargetProviderW944 : Prop :=
  ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
    targetDifferenceSurjectivePrimitiveW923 Y ∧
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y

/-- W944 projects target-difference surjectivity from target no-univ data. -/
def targetDifferenceSurjectivePrimitiveOfTargetNoUnivDataW944
    (targetData : TargetSurjectiveNoUnivMembershipForTargetProviderW944) :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y :=
  fun Y => (targetData Y).1

/-- W944 projects target no-univ compactness from target no-univ data. -/
def targetCodomainCompactNoUnivMembershipPrimitiveOfTargetNoUnivDataW944
    (targetData : TargetSurjectiveNoUnivMembershipForTargetProviderW944) :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y :=
  fun Y => (targetData Y).2

/-- W944 assembles target no-univ data from its two primitive target providers. -/
def targetNoUnivDataOfPrimitiveProvidersW944
    (targetDifferenceSurjectiveProvider :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
        targetDifferenceSurjectivePrimitiveW923 Y)
    (targetCompactNoUnivProvider :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
        targetCodomainCompactNoUnivMembershipPrimitiveW930 Y) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  fun Y =>
    ⟨targetDifferenceSurjectiveProvider Y,
      targetCompactNoUnivProvider Y⟩

/--
W944 preserves W943's boundary, relation, closedness, normalized fixed-target,
source-triangulation, endpoint strict-exact, and localized unit fields, while
bundling the two target primitives into one target no-univ provider.
-/
structure MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
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
W944 projects W943 leaves by unpacking the target no-univ provider.
-/
def w943LeavesOfTargetNoUnivDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    MetrizableWppClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW943
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetDifferenceSurjectiveForTargetProvider :=
    targetDifferenceSurjectivePrimitiveOfTargetNoUnivDataW944
      leaves.targetNoUnivData
  targetCodomainCompactSpaceProvider :=
    targetCodomainCompactNoUnivMembershipPrimitiveOfTargetNoUnivDataW944
      leaves.targetNoUnivData
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointStrictExact := leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    leaves.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W944 W733 concrete leaves after projecting W943 leaves. -/
def concreteLeavesOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
    (w943LeavesOfTargetNoUnivDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
      leaves)

/-- W944 W732 route data after projecting W943 leaves. -/
def routeDataProviderOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
    (w943LeavesOfTargetNoUnivDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
    (w943LeavesOfTargetNoUnivDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW943
    (w943LeavesOfTargetNoUnivDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
      leaves)

/--
W944 exposes W943's route with target-difference surjectivity and
target-codomain no-univ compactness consolidated into one provider.
-/
def closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944 :
    List String :=
  ["bundled W716 WPP-limit boundary data provider: right-open closed-quotient-cover\
      boundary and source-difference cokernel-pi-zero boundary",
    "bundled W717 closed-natural-transformation relation data provider: relation\
      pullback and target-relation lifting",
    "W944 target no-univ data provider: target-difference preimage surjectivity\
      and target-codomain compactness filter nonbottom data",
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

theorem closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944_count :
    closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944.length =
      10 :=
  rfl

/-- Current checked W944 state. -/
structure MetrizableClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW944 :
    Type where
  seed : String
  declarations : List String
  targetNoUnivDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW944 :
    MetrizableClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW944
    where
  seed :=
    "w944-closed-map-target-no-univ-membership-data-closedness-data-boundary-\
      relation-data-normalized-fixed-target-data-source-triangulation-endpoint-\
      strict-exact-unit-strict-exact-components-primitive-field-route"
  declarations :=
    ["TargetSurjectiveNoUnivMembershipForTargetProviderW944",
      "targetDifferenceSurjectivePrimitiveOfTargetNoUnivDataW944",
      "targetCodomainCompactNoUnivMembershipPrimitiveOfTargetNoUnivDataW944",
      "MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944",
      "w943LeavesOfTargetNoUnivDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944",
      "concreteLeavesOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944",
      "routeDataProviderOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944",
      "directBoundedLeftCalculusOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944",
      "boundedDerivedInfinityCategoryOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944",
      "closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944",
      "closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944_count"]
  targetNoUnivDataResult :=
    "proved: W944 target no-univ data projects target-difference surjectivity\
      and W930 target-codomain no-univ compactness required by W943"
  exactAtResult :=
    "proved: closed-map target-no-univ-membership-data-closedness-data-\
      boundary-relation-data-normalized-fixed-target-data-source-triangulation-\
      endpoint-strict-exact-unit-strict-exact-components route feeds the\
      W943/W942/W941/W940/W937/W936/W935/W934/W933/W932/W931/W930 stable\
      ExactAt route"
  refinedInputs :=
    ["target-difference surjectivity and target-codomain no-univ compactness\
      replaced by W944 target no-univ data",
      "normalized strict-representative lift blueprint and both fixed-target\
      uniqueness obligations remain consolidated into W719",
      "selected-difference and mapped-cokernel closedness remain consolidated\
      into W725",
      "boundary and relation leaves remain consolidated into W716 and W717\
      providers",
      "source triangulation remains consolidated into W722"]
  remainingInputs :=
    closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944
  productSuccessClaimed := false

theorem currentW944ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsRouteStateW944;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
